//! Codegen ABI facts derived from the authoritative planned program.
//!
//! Codegen should not rediscover dispatch from raw syntax. This module derives
//! the function-level ABI facts it needs from reachable planned bodies and
//! their resolved call edges.

use crate::fz_ir::{CallsiteId, CallsiteIdent, EmitSlot, FnId, Module, SpecId, Term, Var};
use crate::ir_planner::SpecPlan;
use crate::ir_planner::fn_types::CallableCapability;
use crate::ir_planner::planned::PlannedProgram;
use std::collections::{HashMap, HashSet};

pub(super) struct AbiFacts {
    pub native_fns: HashSet<FnId>,
    pub cont_fns: HashSet<FnId>,
    pub cont_target_fns: HashSet<FnId>,
    pub closure_capture_counts: HashMap<FnId, usize>,
    pub cont_extras_count: HashMap<FnId, usize>,
}

impl AbiFacts {
    pub(super) fn derive(module: &Module, planned_program: &PlannedProgram<'_>) -> Self {
        let mut direct_callees: HashSet<FnId> = HashSet::new();
        let mut cont_fns: HashSet<FnId> = HashSet::new();
        let mut cont_target_fns: HashSet<FnId> = HashSet::new();
        let mut closure_targets: HashSet<FnId> = HashSet::new();
        let mut cont_call_users: HashMap<FnId, Vec<FnId>> = HashMap::new();
        let mut cont_extras_count: HashMap<FnId, usize> = HashMap::new();

        let mut closure_capture_counts: HashMap<FnId, usize> = HashMap::new();
        for (&sid, entry) in planned_program.callable_entries() {
            let fn_id = planned_program.spec_keys()[sid as usize].fn_id;
            closure_targets.insert(fn_id);
            cont_target_fns.insert(fn_id);
            if let Some(previous) = closure_capture_counts.insert(fn_id, entry.capture_count) {
                debug_assert_eq!(
                    previous, entry.capture_count,
                    "closure capture count mismatch for fn {}",
                    fn_id.0
                );
            }
        }

        for &sid in planned_program.reachable_specs() {
            let spec_id = SpecId(sid);
            let planned = planned_program.executable_body(spec_id);
            let plan =
                planned_program.spec_plans()[sid as usize].expect("reachable executable spec must have a SpecPlan");
            for block in &planned.body.blocks {
                if !plan.reachable_blocks.contains(&block.id) {
                    continue;
                }
                match &block.terminator {
                    Term::Call { ident, args, .. } => {
                        let direct = local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Direct, "Direct");
                        let cont = local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Cont, "Cont");
                        direct_callees.insert(direct);
                        cont_fns.insert(cont);
                        cont_target_fns.insert(direct);
                        cont_target_fns.insert(cont);
                        cont_call_users.entry(cont).or_default().push(direct);
                        record_callable_boundary_targets(plan, planned.fn_id, ident, args, &mut closure_capture_counts);
                    }
                    Term::TailCall { ident, args, .. } => {
                        let direct = local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Direct, "Direct");
                        direct_callees.insert(direct);
                        cont_target_fns.insert(direct);
                        record_callable_boundary_targets(plan, planned.fn_id, ident, args, &mut closure_capture_counts);
                    }
                    Term::CallClosure { ident, closure, .. } => {
                        let cont = local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Cont, "Cont");
                        cont_fns.insert(cont);
                        cont_target_fns.insert(cont);
                        if let Some(closure_target) =
                            optional_local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::ClosureCall)
                        {
                            closure_targets.insert(closure_target);
                            cont_target_fns.insert(closure_target);
                        }
                        record_callable_target(plan.callable_capabilities.get(closure), &mut closure_capture_counts);
                    }
                    Term::TailCallClosure { ident, closure, .. } => {
                        if let Some(closure_target) =
                            optional_local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::ClosureCall)
                        {
                            closure_targets.insert(closure_target);
                            cont_target_fns.insert(closure_target);
                        }
                        record_callable_target(plan.callable_capabilities.get(closure), &mut closure_capture_counts);
                    }
                    Term::Receive { ident, .. } => {
                        let cont = local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Cont, "Cont");
                        cont_fns.insert(cont);
                        cont_target_fns.insert(cont);
                        cont_extras_count.insert(cont, 0);
                    }
                    Term::ReceiveMatched { clauses, after, .. } => {
                        for clause in clauses {
                            cont_fns.insert(clause.body);
                            cont_target_fns.insert(clause.body);
                            cont_extras_count.insert(clause.body, 0);
                            if let Some(guard) = clause.guard {
                                cont_fns.insert(guard);
                                cont_target_fns.insert(guard);
                                cont_extras_count.insert(guard, 0);
                            }
                        }
                        if let Some(after) = after {
                            cont_fns.insert(after.body);
                            cont_target_fns.insert(after.body);
                            cont_extras_count.insert(after.body, 0);
                        }
                    }
                    _ => {}
                }
            }
        }
        closure_capture_counts.retain(|fn_id, _| !cont_fns.contains(fn_id));

        let main_id = module.fns.iter().find(|f| f.name == "main").map(|f| f.id);
        let mut native_fns: HashSet<FnId> = HashSet::new();
        for &sid in planned_program.reachable_specs() {
            let fn_id = planned_program.spec_keys()[sid as usize].fn_id;
            if direct_callees.contains(&fn_id)
                || cont_target_fns.contains(&fn_id)
                || closure_targets.contains(&fn_id)
                || Some(fn_id) == main_id
            {
                native_fns.insert(fn_id);
            }
        }
        if let Some(main_id) = main_id {
            native_fns.insert(main_id);
        }

        loop {
            let mut to_remove: Vec<FnId> = Vec::new();
            for &sid in planned_program.reachable_specs() {
                let spec_id = SpecId(sid);
                let planned = planned_program.executable_body(spec_id);
                let plan =
                    planned_program.spec_plans()[sid as usize].expect("reachable executable spec must have a SpecPlan");
                if !native_fns.contains(&planned.fn_id) {
                    continue;
                }
                let body_ok = planned.body.blocks.iter().all(|block| {
                    if !plan.reachable_blocks.contains(&block.id) {
                        return true;
                    }
                    match &block.terminator {
                        Term::Return(_) | Term::Halt(_) | Term::Goto(_, _) | Term::If { .. } => true,
                        Term::Call { ident, .. } => {
                            native_fns.contains(&local_target_fn_id(
                                plan,
                                planned.fn_id,
                                ident,
                                EmitSlot::Direct,
                                "Direct",
                            )) && native_fns.contains(&local_target_fn_id(
                                plan,
                                planned.fn_id,
                                ident,
                                EmitSlot::Cont,
                                "Cont",
                            ))
                        }
                        Term::TailCall { ident, .. } => native_fns.contains(&local_target_fn_id(
                            plan,
                            planned.fn_id,
                            ident,
                            EmitSlot::Direct,
                            "Direct",
                        )),
                        Term::CallClosure { ident, .. } => {
                            optional_local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::ClosureCall)
                                .is_none_or(|target| native_fns.contains(&target))
                                && native_fns.contains(&local_target_fn_id(
                                    plan,
                                    planned.fn_id,
                                    ident,
                                    EmitSlot::Cont,
                                    "Cont",
                                ))
                        }
                        Term::TailCallClosure { ident, .. } => {
                            optional_local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::ClosureCall)
                                .is_none_or(|target| native_fns.contains(&target))
                        }
                        Term::Receive { ident, .. } => {
                            native_fns.contains(&local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Cont, "Cont"))
                        }
                        Term::ReceiveMatched { clauses, after, .. } => {
                            let clauses_ok = clauses.iter().all(|clause| {
                                native_fns.contains(&clause.body)
                                    && clause.guard.is_none_or(|guard| native_fns.contains(&guard))
                            });
                            let after_ok = after.as_ref().is_none_or(|after| native_fns.contains(&after.body));
                            clauses_ok && after_ok
                        }
                    }
                });
                let cont_users_ok = cont_call_users
                    .get(&planned.fn_id)
                    .is_none_or(|users| users.iter().all(|callee| native_fns.contains(callee)));
                if !body_ok || !cont_users_ok {
                    to_remove.push(planned.fn_id);
                }
            }
            if to_remove.is_empty() {
                break;
            }
            for fn_id in to_remove {
                native_fns.remove(&fn_id);
            }
        }
        native_fns.extend(cont_fns.iter().copied());
        native_fns.extend(closure_capture_counts.keys().copied());
        loop {
            let mut changed = false;
            for &sid in planned_program.reachable_specs() {
                let spec_id = SpecId(sid);
                let planned = planned_program.executable_body(spec_id);
                if !native_fns.contains(&planned.fn_id) {
                    continue;
                }
                let plan =
                    planned_program.spec_plans()[sid as usize].expect("reachable executable spec must have a SpecPlan");
                for block in &planned.body.blocks {
                    if !plan.reachable_blocks.contains(&block.id) {
                        continue;
                    }
                    let mut add_target = |target: FnId, native_fns: &mut HashSet<FnId>| {
                        if native_fns.insert(target) {
                            changed = true;
                        }
                    };
                    match &block.terminator {
                        Term::Call { ident, .. } => {
                            add_target(
                                local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Direct, "Direct"),
                                &mut native_fns,
                            );
                            add_target(
                                local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Cont, "Cont"),
                                &mut native_fns,
                            );
                        }
                        Term::TailCall { ident, .. } => {
                            add_target(
                                local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Direct, "Direct"),
                                &mut native_fns,
                            );
                        }
                        Term::CallClosure { ident, .. } => {
                            if let Some(target) =
                                optional_local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::ClosureCall)
                            {
                                add_target(target, &mut native_fns);
                            }
                            add_target(
                                local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Cont, "Cont"),
                                &mut native_fns,
                            );
                        }
                        Term::TailCallClosure { ident, .. } => {
                            if let Some(target) =
                                optional_local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::ClosureCall)
                            {
                                add_target(target, &mut native_fns);
                            }
                        }
                        Term::Receive { ident, .. } => {
                            add_target(
                                local_target_fn_id(plan, planned.fn_id, ident, EmitSlot::Cont, "Cont"),
                                &mut native_fns,
                            );
                        }
                        Term::ReceiveMatched { clauses, after, .. } => {
                            for clause in clauses {
                                add_target(clause.body, &mut native_fns);
                                if let Some(guard) = clause.guard {
                                    add_target(guard, &mut native_fns);
                                }
                            }
                            if let Some(after) = after {
                                add_target(after.body, &mut native_fns);
                            }
                        }
                        _ => {}
                    }
                }
            }
            if !changed {
                break;
            }
        }

        Self {
            native_fns,
            cont_fns,
            cont_target_fns,
            closure_capture_counts,
            cont_extras_count,
        }
    }
}

fn local_target_fn_id(plan: &SpecPlan, caller: FnId, ident: &CallsiteIdent, slot: EmitSlot, slot_name: &str) -> FnId {
    plan.local_call_target(&CallsiteId::new(caller, ident, slot))
        .unwrap_or_else(|| {
            panic!(
                "reachable planned body missing {} dispatch at caller {}",
                slot_name, caller.0
            )
        })
        .fn_id
}

fn optional_local_target_fn_id(plan: &SpecPlan, caller: FnId, ident: &CallsiteIdent, slot: EmitSlot) -> Option<FnId> {
    plan.local_call_target(&CallsiteId::new(caller, ident, slot))
        .map(|target| target.fn_id)
}

fn record_callable_boundary_targets(
    plan: &SpecPlan,
    caller: FnId,
    ident: &CallsiteIdent,
    args: &[Var],
    closure_capture_counts: &mut HashMap<FnId, usize>,
) {
    let boundary_callsite = CallsiteId::new(caller, ident, EmitSlot::CallableBoundary);
    if plan.local_call_target(&boundary_callsite).is_none() {
        return;
    }
    for arg in args {
        record_callable_target(plan.callable_capabilities.get(arg), closure_capture_counts);
    }
}

fn record_callable_target(capability: Option<&CallableCapability>, closure_capture_counts: &mut HashMap<FnId, usize>) {
    let Some((fn_id, capture_count)) = (match capability {
        Some(CallableCapability::KnownFn(fn_id)) => Some((*fn_id, 0)),
        Some(CallableCapability::KnownClosure { fn_id, captures, .. }) => Some((*fn_id, captures.len())),
        Some(CallableCapability::OpaqueCallable) | None => None,
    }) else {
        return;
    };
    if let Some(previous) = closure_capture_counts.insert(fn_id, capture_count) {
        debug_assert_eq!(
            previous, capture_count,
            "closure capture count mismatch for fn {}",
            fn_id.0
        );
    }
}
