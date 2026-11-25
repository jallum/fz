//! An executable's body with every clause and entry its analysis proved
//! unreachable removed.

use std::cell::OnceCell;
use std::fmt;

use crate::fast_hash::{HashMap, HashSet};

use super::body::{ControlDestination, ControlEntryId, LoweredBody, LoweredClause, LoweredEntry, LoweredTail};
use super::executable_facts::ExecutableFacts;

pub(crate) struct PrunedLoweredBody {
    pub(crate) body: LoweredBody,
    pub(crate) original_entry_ids: Vec<ControlEntryId>,
}

/// The executable's body with every clause and entry its analysis proved
/// unreachable removed. Every transport position an artifact asks for is a
/// position of this body.
fn prune_executable_body(facts: &ExecutableFacts) -> PrunedLoweredBody {
    let analysis = facts.analysis();
    let lowered = facts.body();
    let (dispatch_outcomes, retained_entries) = if facts.extern_wire().is_some() {
        // An extern has no clauses or entries to prune: `analysis` may still
        // carry reachability evidence keyed to a body this executable does
        // not have, and clause/entry ids from that evidence do not index
        // into an empty body.
        (Vec::new(), Vec::new())
    } else {
        let LoweredBody::Clauses { clauses, .. } = lowered;
        let mut entries = analysis.reachable_entries.clone();
        entries.extend(
            analysis
                .entry_reachability
                .clauses()
                .iter()
                .map(|clause| clauses[*clause as usize].entry),
        );
        entries.sort_by_key(|entry| entry.as_u32());
        entries.dedup();
        (analysis.entry_reachability.clauses().to_vec(), entries)
    };
    prune_lowered_body(lowered, &dispatch_outcomes, &retained_entries)
}

fn prune_lowered_body(
    body: &LoweredBody,
    reachable_clauses: &[u32],
    reachable_entries: &[ControlEntryId],
) -> PrunedLoweredBody {
    let value_count = body.value_count();
    let LoweredBody::Clauses {
        clauses,
        entries,
        generated,
        entry_plan,
        ..
    } = body;
    let reachable_entries = reachable_entries.iter().copied().collect::<HashSet<_>>();
    let mut clauses = reachable_clauses
        .iter()
        .map(|clause_id| clauses[*clause_id as usize].clone())
        .collect::<Vec<_>>();
    let mut needed = HashMap::default();
    let mut kept_ids = Vec::new();
    for clause in &clauses {
        collect_reachable_entries(entries, clause.entry, &reachable_entries, &mut kept_ids, &mut needed);
    }
    let mut kept = kept_ids
        .iter()
        .map(|entry_id| {
            specialize_entry(
                &entries[entry_id.as_u32() as usize],
                reachable_entries.contains(entry_id),
            )
        })
        .collect::<Vec<_>>();
    reindex_entries(&mut clauses, &mut kept, &needed);
    PrunedLoweredBody {
        body: LoweredBody::clauses(clauses, kept, generated.clone())
            .with_entry_plan_of(entry_plan)
            .with_value_count(value_count),
        original_entry_ids: kept_ids,
    }
}

fn collect_reachable_entries(
    entries: &[LoweredEntry],
    entry_id: ControlEntryId,
    reachable_entries: &HashSet<ControlEntryId>,
    order: &mut Vec<ControlEntryId>,
    out: &mut HashMap<ControlEntryId, ControlEntryId>,
) {
    if out.contains_key(&entry_id) {
        return;
    }
    let next_id = ControlEntryId::from_u32(order.len() as u32);
    order.push(entry_id);
    out.insert(entry_id, next_id);
    if !reachable_entries.contains(&entry_id) {
        return;
    }
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        LoweredTail::Value { dest, .. }
        | LoweredTail::DirectCall { dest, .. }
        | LoweredTail::ClosureCall { dest, .. } => {
            if let ControlDestination::Deliver(target) = dest {
                collect_reachable_entries(entries, *target, reachable_entries, order, out);
            }
        }
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            collect_reachable_entries(entries, *then_entry, reachable_entries, order, out);
            collect_reachable_entries(entries, *else_entry, reachable_entries, order, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for target in dispatch.successors() {
                collect_reachable_entries(entries, target, reachable_entries, order, out);
            }
        }
        LoweredTail::Receive(receive) => {
            if let ControlDestination::Deliver(target) = &receive.dest {
                collect_reachable_entries(entries, *target, reachable_entries, order, out);
            }
            for clause in &receive.outcomes {
                collect_reachable_entries(entries, clause.target, reachable_entries, order, out);
            }
            if let Some(after) = &receive.after {
                collect_reachable_entries(entries, after.entry, reachable_entries, order, out);
            }
        }
        LoweredTail::Try { body, handler } => {
            collect_reachable_entries(entries, *body, reachable_entries, order, out);
            collect_reachable_entries(entries, *handler, reachable_entries, order, out);
        }
        LoweredTail::Unreachable => {}
    }
}

fn specialize_entry(entry: &LoweredEntry, is_reachable: bool) -> LoweredEntry {
    if is_reachable {
        return entry.clone();
    }
    LoweredEntry {
        span: entry.span,
        origin: entry.origin.clone(),
        params: entry.params.clone(),
        captures: entry.captures.clone(),
        capture_owners: entry.capture_owners.clone(),
        physical_captures: entry.physical_captures.clone(),
        physical_params: entry.physical_params.clone(),
        steps: Vec::new(),
        tail: LoweredTail::Unreachable,
    }
}

fn reindex_entries(
    clauses: &mut [LoweredClause],
    entries: &mut [LoweredEntry],
    ids: &HashMap<ControlEntryId, ControlEntryId>,
) {
    for clause in clauses {
        clause.entry = ids[&clause.entry];
    }
    for entry in entries {
        for owner in &mut entry.capture_owners {
            owner.entry = ids[&owner.entry];
        }
        match &mut entry.tail {
            LoweredTail::Value { dest, .. }
            | LoweredTail::DirectCall { dest, .. }
            | LoweredTail::ClosureCall { dest, .. } => {
                if let ControlDestination::Deliver(target) = dest {
                    *target = ids[target];
                }
            }
            LoweredTail::If {
                then_entry, else_entry, ..
            } => {
                *then_entry = ids[then_entry];
                *else_entry = ids[else_entry];
            }
            LoweredTail::Dispatch { dispatch, .. } => {
                for target in dispatch.successors_mut() {
                    *target = ids[target];
                }
            }
            LoweredTail::Receive(receive) => {
                if let ControlDestination::Deliver(target) = &mut receive.dest {
                    *target = ids[target];
                }
                for clause in &mut receive.outcomes {
                    clause.target = ids[&clause.target];
                }
                if let Some(after) = &mut receive.after {
                    after.entry = ids[&after.entry];
                }
            }
            LoweredTail::Try { body, handler } => {
                *body = ids[body];
                *handler = ids[handler];
            }
            LoweredTail::Unreachable => {}
        }
    }
}

/// An executable's pruned body, derived the first time anyone asks and
/// remembered with the facts it is a view of. Facts are immutable once
/// published, so the view cannot go stale; it takes no part in what makes two
/// facts equal.
#[derive(Default)]
pub(crate) struct PrunedBodyMemo(OnceCell<PrunedLoweredBody>);

impl PrunedBodyMemo {
    pub(super) fn of(&self, facts: &ExecutableFacts) -> &PrunedLoweredBody {
        self.0.get_or_init(|| prune_executable_body(facts))
    }
}

impl PartialEq for PrunedBodyMemo {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl Clone for PrunedBodyMemo {
    fn clone(&self) -> Self {
        Self::default()
    }
}

impl fmt::Debug for PrunedBodyMemo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("PrunedBodyMemo")
    }
}

#[cfg(test)]
#[path = "pruned_body_test.rs"]
mod pruned_body_test;
