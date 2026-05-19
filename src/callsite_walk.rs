//! fz-9pr.17 (fz-CO.D.0) — block-callsite enumerator shared by the
//! reducer and the typer's discovery walk.
//!
//! Three passes (reducer, `walk_spec_for_discovery` in ir_typer, and
//! historically ir_inline) each duplicated the mapping from a block's
//! terminator to "which callsite slots does it contribute, and what
//! does each one target." This module hosts that mapping once.
//!
//! ## What it yields
//!
//! Given a block and a per-Var Descr env (caller-side: typer uses
//! `block_envs`, reducer uses its fold env), `block_callsites` produces
//! the *structural* list of callsite slots the block's terminator
//! contributes. Each entry carries the `EmitSlot` plus the data the
//! consumer needs to (a) look up / rewrite the actual term and
//! (b) compute its target spec key:
//!
//!   - `Direct` — callee `FnId`, arg `Var`s.
//!   - `CallClosureKnown` — resolved target `FnId` (via fn_constants),
//!     arg `Var`s.
//!   - `ClosureLit(c, s)` — target `FnId` from the lit, captures,
//!     arg `Var`s.
//!   - `Cont` — continuation `FnId` + captured `Var`s, plus a tag
//!     that names the slot-0 source (callee return / closure return
//!     / receive).
//!
//! ## What it does NOT yield
//!
//! - `MakeClosure(stmt_idx)` — stmt-level, lives on its own per-block
//!   loop because it's gated on opaque-arity liveness (typer-only).
//! - The opaque-arity bookkeeping that feeds `opaque_arities_seen`.
//! - Per-spec Descr keys — consumers build those from the structural
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
//! / `EmitSlot::ClosureLit(0, 0)` literals scattered across the four
//! arms of `reduce_terminator`.

use crate::fz_ir::{Cont, EmitSlot, FnId, Term, Var};
use crate::types::{ClosureLit, Descr};
use std::collections::HashMap;

/// fz-9pr.17 — one structural callsite produced by a block's terminator.
///
/// `slot` is the canonical `EmitSlot` (Direct / CallClosureKnown /
/// ClosureLit(c, s) / Cont). `kind` carries the data both the typer's
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
    /// Var resolved through `fn_constants` to a static FnId. Distinct
    /// from `Direct` because the same block can simultaneously emit a
    /// `Cont` for the same Call.
    CallClosureKnown { target: FnId, args: &'a [Var] },
    /// `Term::CallClosure` / `Term::TailCallClosure` whose `closure`
    /// Var has a Descr containing a closure_lit for `(clause_idx,
    /// sig_idx)`. Captures are spliced ahead of `args` when building
    /// the target key.
    ClosureLit {
        lit: &'a ClosureLit,
        args: &'a [Var],
    },
    /// Continuation of `Term::Call` / `Term::CallClosure` /
    /// `Term::Receive`. Slot 0 of the cont's key is the value flowing
    /// in (callee return, closure return, or the received message);
    /// `cont.captured[i]` lands at param slot `i + 1`.
    Cont {
        cont: &'a Cont,
        source: ContSource<'a>,
    },
}

/// fz-9pr.17 — names the source of slot 0 for a `Cont` callsite so the
/// typer's key-builder can fetch the right effective_return / use the
/// right `any` semantics.
#[derive(Clone)]
pub enum ContSource<'a> {
    /// `Term::Call`: slot 0 = `effective_returns[(callee, arg_descrs)]`.
    Call { callee: FnId, args: &'a [Var] },
    /// `Term::CallClosure`: slot 0 = effective_return of the closure
    /// target (fn_constants path) OR resolved via closure-lit lattice.
    /// Both paths use `closure`/`args`.
    CallClosure { closure: Var, args: &'a [Var] },
    /// `Term::Receive`: slot 0 is opaque (`any`).
    Receive,
}

/// fz-9pr.17 — enumerate the terminator-derived callsites of `block`.
///
/// `env` is the caller-side per-Var Descr env at the *end* of the
/// block's stmt sequence; used to extract a `closure` Var's
/// closure_lit Descr when the terminator is `CallClosure` /
/// `TailCallClosure`. `fn_constants` is the caller spec's resolved
/// Var → FnId map (typer-side); the reducer passes an empty map and
/// gets no `CallClosureKnown` entries — its closure_lit path comes
/// from the lit Descr alone.
///
/// Block-stmt callsites (`Prim::MakeClosure`) and per-stmt
/// opaque-arity bookkeeping are *not* yielded — they're typer-specific
/// and live on the typer's own per-stmt loop.
pub fn block_callsites<'a>(
    term: &'a Term,
    env: &'a HashMap<Var, Descr>,
    fn_constants: &HashMap<Var, FnId>,
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
                kind: CallsiteKind::Direct {
                    callee: *callee,
                    args,
                },
            });
            out.push(BlockCallsite {
                slot: EmitSlot::Cont,
                kind: CallsiteKind::Cont {
                    cont: continuation,
                    source: ContSource::Call {
                        callee: *callee,
                        args,
                    },
                },
            });
        }
        Term::TailCall { callee, args, .. } => {
            out.push(BlockCallsite {
                slot: EmitSlot::Direct,
                kind: CallsiteKind::Direct {
                    callee: *callee,
                    args,
                },
            });
        }
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
        } => {
            push_closure_call(&mut out, *closure, args, env, fn_constants);
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
            push_closure_call(&mut out, *closure, args, env, fn_constants);
        }
        Term::Receive {
            continuation,
            ident: _,
        } => {
            out.push(BlockCallsite {
                slot: EmitSlot::Cont,
                kind: CallsiteKind::Cont {
                    cont: continuation,
                    source: ContSource::Receive,
                },
            });
        }
        Term::If { .. } | Term::Goto(..) | Term::Return(..) | Term::Halt(..) => {}
    }
    out
}

fn push_closure_call<'a>(
    out: &mut Vec<BlockCallsite<'a>>,
    closure: Var,
    args: &'a [Var],
    env: &'a HashMap<Var, Descr>,
    fn_constants: &HashMap<Var, FnId>,
) {
    // fn_constants path — emits CallClosureKnown.
    if let Some(&target) = fn_constants.get(&closure) {
        out.push(BlockCallsite {
            slot: EmitSlot::CallClosureKnown,
            kind: CallsiteKind::CallClosureKnown { target, args },
        });
    }
    // closure_lit path — one callsite per (clause_idx, sig_idx) with
    // a lit. Same iteration order as `walk_spec_for_discovery`'s
    // pre-refactor body; goldens depend on it.
    if let Some(cv_descr) = env.get(&closure) {
        for (c_idx, clause) in cv_descr.funcs.iter().enumerate() {
            if !clause.neg.is_empty() {
                continue;
            }
            for (s_idx, sig) in clause.pos.iter().enumerate() {
                let Some(lit) = &sig.lit else {
                    continue;
                };
                out.push(BlockCallsite {
                    slot: EmitSlot::ClosureLit(c_idx, s_idx),
                    kind: CallsiteKind::ClosureLit { lit, args },
                });
            }
        }
    }
}

/// fz-9pr.17 — the canonical `EmitSlot` the reducer should record
/// against when its fold attempt at a block's terminator succeeds or
/// stalls. Returns `None` for non-call terminators.
///
/// The reducer used to spell `EmitSlot::Direct` / `EmitSlot::ClosureLit(0, 0)`
/// inline at four match arms; this routes those through one site.
/// `ClosureLit(0, 0)` mirrors the pre-refactor reducer's choice (the
/// reducer doesn't distinguish per-(c, s) because it only ever folds a
/// single closure-call site per block).
pub fn slot_for_term(term: &Term) -> Option<EmitSlot> {
    match term {
        Term::Call { .. } | Term::TailCall { .. } => Some(EmitSlot::Direct),
        Term::CallClosure { .. } | Term::TailCallClosure { .. } => Some(EmitSlot::ClosureLit(0, 0)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{BlockId, Cont, FnId, Term, Var};

    fn empty_env() -> HashMap<Var, Descr> {
        HashMap::new()
    }
    fn empty_fc() -> HashMap<Var, FnId> {
        HashMap::new()
    }

    #[test]
    fn empty_for_non_call_terms() {
        let env = empty_env();
        let fc = empty_fc();
        assert!(block_callsites(&Term::Goto(BlockId(0), vec![]), &env, &fc).is_empty());
        assert!(
            block_callsites(&Term::if_user(Var(0), BlockId(0), BlockId(1)), &env, &fc).is_empty()
        );
        assert!(block_callsites(&Term::Return(Var(0)), &env, &fc).is_empty());
        assert!(block_callsites(&Term::Halt(Var(0)), &env, &fc).is_empty());
    }

    #[test]
    fn tail_call_yields_direct_only() {
        let t = Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::synthetic(),
            callee: FnId(7),
            args: vec![Var(1), Var(2)],
            is_back_edge: false,
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&t, &env, &fc);
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
        let t = Term::Call {
            ident: crate::fz_ir::CallsiteIdent::synthetic(),
            callee: FnId(5),
            args: vec![Var(1)],
            continuation: Cont {
                fn_id: FnId(9),
                captured: vec![Var(2)],
            },
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&t, &env, &fc);
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
        let t = Term::TailCallClosure {
            ident: crate::fz_ir::CallsiteIdent::synthetic(),
            closure: Var(3),
            args: vec![Var(1)],
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&t, &env, &fc);
        assert!(cs.is_empty());
    }

    #[test]
    fn tail_call_closure_fn_constants_yields_known() {
        let t = Term::TailCallClosure {
            ident: crate::fz_ir::CallsiteIdent::synthetic(),
            closure: Var(3),
            args: vec![Var(1)],
        };
        let env = empty_env();
        let mut fc = empty_fc();
        fc.insert(Var(3), FnId(11));
        let cs = block_callsites(&t, &env, &fc);
        assert_eq!(cs.len(), 1);
        assert!(matches!(cs[0].slot, EmitSlot::CallClosureKnown));
    }

    #[test]
    fn call_closure_yields_cont_when_closure_unresolved() {
        let t = Term::CallClosure {
            ident: crate::fz_ir::CallsiteIdent::synthetic(),
            closure: Var(3),
            args: vec![Var(1)],
            continuation: Cont {
                fn_id: FnId(9),
                captured: vec![],
            },
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&t, &env, &fc);
        assert_eq!(cs.len(), 1);
        assert!(matches!(cs[0].slot, EmitSlot::Cont));
    }

    #[test]
    fn receive_yields_cont_with_receive_source() {
        let t = Term::Receive {
            ident: crate::fz_ir::CallsiteIdent::synthetic(),
            continuation: Cont {
                fn_id: FnId(9),
                captured: vec![],
            },
        };
        let env = empty_env();
        let fc = empty_fc();
        let cs = block_callsites(&t, &env, &fc);
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
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![],
                is_back_edge: false
            }),
            Some(EmitSlot::Direct)
        ));
        assert!(matches!(
            slot_for_term(&Term::TailCallClosure {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                closure: Var(0),
                args: vec![]
            }),
            Some(EmitSlot::ClosureLit(0, 0))
        ));
        assert!(slot_for_term(&Term::Halt(Var(0))).is_none());
    }
}
