//! fz-uwq.14 — debug-build invariant assertion for the codegen pipeline.
//!
//! Premise: once the typer commits to specs in `type_module`, the
//! post-typer passes (branch_fold, fold, const_bs::fold, dce_module,
//! dce_module_level) may *consume* call-shape terminators (fold them
//! into Returns / Gotos) but must never *invent* new ones. The typer's
//! spec set wouldn't cover an invented call.
//!
//! The check: snapshot per-fn call-shape multisets right after the
//! typer. After the final post-typer pass, snapshot again and assert
//! that every (FnId, CallShape) count in the post snapshot is ≤ its
//! pre snapshot count.
//!
//! Catches future contributors who add a post-typer pass that
//! accidentally introduces a new Term::Call etc — a class of bug
//! that would silently miscompile (codegen would dispatch through
//! `FnTypes.dispatches`, find no entry, and either panic or pick the
//! wrong target).

use crate::fz_ir::{FnId, Module, Term};
use std::collections::HashMap;

/// Tag identifying the kind of call-shape a terminator has.
/// `None` (the absence of a tag) is implied for non-call terminators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CallShape {
    Call,
    TailCall,
    CallClosure,
    TailCallClosure,
    Receive,
}

fn shape_of(t: &Term) -> Option<CallShape> {
    match t {
        Term::Call { .. } => Some(CallShape::Call),
        Term::TailCall { .. } => Some(CallShape::TailCall),
        Term::CallClosure { .. } => Some(CallShape::CallClosure),
        Term::TailCallClosure { .. } => Some(CallShape::TailCallClosure),
        Term::Receive { .. } => Some(CallShape::Receive),
        _ => None,
    }
}

/// Per-fn multiset of call-shape tags across all blocks.
pub type CallShapeSnapshot = HashMap<FnId, HashMap<CallShape, usize>>;

pub fn snapshot_call_shapes(m: &Module) -> CallShapeSnapshot {
    let mut out: CallShapeSnapshot = HashMap::new();
    for f in &m.fns {
        let mut counts: HashMap<CallShape, usize> = HashMap::new();
        for b in &f.blocks {
            if let Some(s) = shape_of(&b.terminator) {
                *counts.entry(s).or_insert(0) += 1;
            }
        }
        if !counts.is_empty() {
            out.insert(f.id, counts);
        }
    }
    out
}

/// Assert that no fn gained new call shapes between the two snapshots.
/// A fn that was DCE-ed out entirely (no entry in the post snapshot) is
/// fine — the post-typer pipeline may prune unreachable fns.
pub fn assert_no_new_call_shapes(m: &Module, pre: &CallShapeSnapshot) {
    let post = snapshot_call_shapes(m);
    for (fid, post_counts) in &post {
        let empty = HashMap::new();
        let pre_counts = pre.get(fid).unwrap_or(&empty);
        for (shape, post_n) in post_counts {
            let pre_n = pre_counts.get(shape).copied().unwrap_or(0);
            assert!(
                *post_n <= pre_n,
                "fz-uwq.14: fn {:?} has {} {:?} terminators post-codegen but only {} \
                 post-typer — a post-typer pass invented call shapes the typer's \
                 specs don't cover",
                fid,
                post_n,
                shape,
                pre_n
            );
        }
    }
}
