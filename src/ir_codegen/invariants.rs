//! Debug-build invariant: post-typer passes may *consume* call-shape
//! terminators (folding into Returns / Gotos) but must never *invent*
//! new ones — the typer's spec set wouldn't cover an invented call,
//! and codegen would dispatch through `SpecPlan.call_edges`, find no
//! entry, and either panic or pick the wrong target.
//!
//! Snapshot per-fn call-shape multisets right after the typer, then
//! again after the final post-typer pass; every (FnId, CallShape) count
//! in the post snapshot must be ≤ its pre snapshot count.

use crate::fz_ir::{CallsiteId, EmitSlot, FnId, Module, Term};
use std::collections::HashMap;

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
                "fn {:?} has {} {:?} terminators post-codegen but only {} \
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

pub fn emit_and_assert_spec_dispatch_coverage(
    tel: &dyn crate::telemetry::Telemetry,
    f: &crate::fz_ir::FnIr,
    ft: &crate::ir_planner::SpecPlan,
    sid: u32,
    spec_key: &crate::ir_planner::fn_types::SpecKey,
) {
    let mut closure_call_dispatch_count = 0_u64;
    let (body_counts, body_callsites) = crate::ir_planner::inventory::body_callsite_inventory(f);
    let plan_call_edges = crate::ir_planner::inventory::plan_call_edge_inventory(ft, f.id);

    for blk in &f.blocks {
        if !ft.reachable_blocks.contains(&blk.id) {
            continue;
        }
        let (ident, expected_slots, kind) = match &blk.terminator {
            Term::Call { ident, .. } => (ident, &[EmitSlot::Direct, EmitSlot::Cont][..], "call"),
            Term::CallClosure { ident, .. } => {
                let closure_callsite = CallsiteId::new(f.id, ident, EmitSlot::ClosureCall);
                if ft.local_call_target(&closure_callsite).is_some() {
                    closure_call_dispatch_count += 1;
                }
                (ident, &[EmitSlot::Cont][..], "call_closure")
            }
            Term::Receive { ident, .. } => (ident, &[EmitSlot::Cont][..], "receive"),
            _ => continue,
        };

        for slot in expected_slots {
            let cid = CallsiteId::new(f.id, ident, *slot);
            if ft.local_call_target(&cid).is_some() {
                continue;
            }
            let available_slots = ft
                .call_edges
                .keys()
                .filter(|candidate| candidate.caller == f.id && candidate.ident == *ident)
                .map(|candidate| format!("{:?}", candidate.slot))
                .collect::<Vec<_>>();
            let available_call_edges = ft
                .call_edges
                .iter()
                .map(|(candidate, edge)| format!("{:?} -> {:?}", candidate, edge.target))
                .collect::<Vec<_>>();
            let span = ident.span();
            tel.execute(
                &["fz", "codegen", "dispatch_missing"],
                &crate::measurements! {},
                &crate::metadata! {
                    spec_id: sid as u64,
                    body_fn_id: f.id.0 as u64,
                    body_name: f.name.clone(),
                    block_id: blk.id.0 as u64,
                    term_kind: kind,
                    slot: format!("{:?}", slot),
                    callsite_span_start: span.start as u64,
                    callsite_span_end: span.end as u64,
                    available_slots: available_slots.clone(),
                    available_call_edges: available_call_edges.clone(),
                },
            );
            panic!(
                "spec {} body {} missing {:?} dispatch for {:?}; available slots: {:?}; call edges: {:?}",
                sid, f.name, slot, cid, available_slots, available_call_edges
            );
        }
    }

    tel.execute(
        &["fz", "codegen", "spec_pair_inventory"],
        &crate::measurements! {
            non_tail_call_count: body_counts.non_tail_call_count,
            non_tail_closure_call_count: body_counts.non_tail_closure_call_count,
            tail_call_count: body_counts.tail_call_count,
            tail_closure_call_count: body_counts.tail_closure_call_count,
            closure_call_dispatch_count: closure_call_dispatch_count,
            receive_count: body_counts.receive_count,
            call_edge_count: ft.call_edges.len() as u64,
        },
        &crate::metadata! {
            spec_id: sid as u64,
            spec_key: format!("{:?}", spec_key),
            body_fn_id: f.id.0 as u64,
            body_name: f.name.clone(),
            body_callsites: body_callsites,
            plan_call_edges: plan_call_edges,
        },
    );
}
