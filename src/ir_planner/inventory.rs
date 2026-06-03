use crate::fz_ir::{EmitSlot, FnId, FnIr, Term};
use crate::ir_planner::SpecPlan;

#[derive(Debug, Clone, Copy, Default)]
pub struct BodyCallsiteCounts {
    pub non_tail_call_count: u64,
    pub non_tail_closure_call_count: u64,
    pub tail_call_count: u64,
    pub tail_closure_call_count: u64,
    pub receive_count: u64,
}

pub fn body_callsite_inventory(f: &FnIr) -> (BodyCallsiteCounts, Vec<String>) {
    let mut counts = BodyCallsiteCounts::default();
    let mut inventory = Vec::new();
    for blk in &f.blocks {
        let Some(ident) = blk.terminator.ident() else {
            continue;
        };
        let span = ident.span();
        let label = match &blk.terminator {
            Term::Call { .. } => {
                counts.non_tail_call_count += 1;
                "call"
            }
            Term::CallClosure { .. } => {
                counts.non_tail_closure_call_count += 1;
                "call_closure"
            }
            Term::TailCall { .. } => {
                counts.tail_call_count += 1;
                "tail_call"
            }
            Term::TailCallClosure { .. } => {
                counts.tail_closure_call_count += 1;
                "tail_call_closure"
            }
            Term::Receive { .. } => {
                counts.receive_count += 1;
                "receive"
            }
            Term::ReceiveMatched { .. } => "receive_matched",
            _ => continue,
        };
        inventory.push(format!("{}#b{}@{}..{}", label, blk.id.0, span.start, span.end));
    }
    inventory.sort();
    (counts, inventory)
}

pub fn plan_call_edge_inventory(ft: &SpecPlan, caller: FnId) -> Vec<String> {
    let mut inventory = ft
        .call_edges
        .keys()
        .filter(|cid| cid.caller == caller)
        .map(|cid| {
            let span = cid.ident.span();
            let slot = match cid.slot {
                EmitSlot::Direct => "direct",
                EmitSlot::Cont => "cont",
                EmitSlot::ClosureCall => "closure_call",
                EmitSlot::CallableBoundary => "callable_boundary",
            };
            format!("{}@{}..{}", slot, span.start, span.end)
        })
        .collect::<Vec<_>>();
    inventory.sort();
    inventory
}
