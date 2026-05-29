use super::fn_types::{FnEffects, ReturnContextPlan, ReturnDemand, SpecKey};
use crate::callsite_walk::ContSource;
use crate::fz_ir::{FnId, FnIr, Module, Prim, Stmt, Term, Var, prim_uses_var, term_uses_var};
use std::collections::{HashMap, HashSet};

pub(crate) fn direct_call_return_plan<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &Module,
    fn_effects: &FnEffects,
    caller_spec_key: &SpecKey,
    env: &HashMap<Var, crate::types::Ty>,
    callee: FnId,
    args: &[Var],
    continuation: &crate::fz_ir::Cont,
) -> (ReturnDemand, Option<ReturnContextPlan>) {
    if let Some((pivot, tail, tail_ty)) =
        cons_then_direct_list_tail_plan(m, caller_spec_key, callee, args, continuation)
    {
        let demand = if caller_spec_key.demand.tuple_field_arity().is_none() {
            ReturnDemand::list_tail(tail_ty.clone())
        } else {
            return_demand_for_call(t, m, fn_effects, env, callee, continuation)
        };
        return (
            demand,
            Some(ReturnContextPlan::ConsThenDirect {
                continuation: continuation.fn_id,
                pivot,
                tail,
                tail_ty,
            }),
        );
    }

    let demand = return_demand_for_call(t, m, fn_effects, env, callee, continuation);
    let context_plan = direct_call_return_context_plan(m, caller_spec_key, continuation, &demand);
    (demand, context_plan)
}

pub(crate) fn tail_call_return_plan(
    m: &Module,
    caller_spec_key: &SpecKey,
    callee: FnId,
    args: &[Var],
) -> (ReturnDemand, Option<ReturnContextPlan>) {
    let demand = if caller_spec_key.demand.tuple_field_arity().is_some()
        && is_continuation_fn(m, caller_spec_key.fn_id)
    {
        match caller_spec_key.demand.list_tail_ty() {
            Some(tail_ty) => ReturnDemand::list_tail(tail_ty.clone()),
            None => ReturnDemand::value(),
        }
    } else {
        caller_spec_key.demand.clone()
    };
    let context_plan = match demand.list_tail_ty() {
        Some(tail_ty) if args.len() >= 2 => Some(ReturnContextPlan::TailCallDestination {
            callee,
            source: args[0],
            tail: args[1],
            tail_ty: tail_ty.clone(),
        }),
        _ => None,
    };
    (demand, context_plan)
}

fn is_continuation_fn(m: &Module, fn_id: FnId) -> bool {
    m.fns.iter().any(|f| {
        f.blocks.iter().any(|b| match &b.terminator {
            Term::Call { continuation, .. }
            | Term::CallClosure { continuation, .. }
            | Term::Receive { continuation, .. } => continuation.fn_id == fn_id,
            Term::ReceiveMatched { clauses, after, .. } => {
                clauses
                    .iter()
                    .any(|clause| clause.body == fn_id || clause.guard == Some(fn_id))
                    || after.as_ref().is_some_and(|after| after.body == fn_id)
            }
            _ => false,
        })
    })
}

pub(crate) fn continuation_return_demand(
    m: &Module,
    caller_spec_key: &SpecKey,
    cont: &crate::fz_ir::Cont,
    source: &ContSource,
) -> ReturnDemand {
    let ContSource::Call { callee, .. } = source else {
        return ReturnDemand::value();
    };
    if let Some(tail_ty) = caller_spec_key.demand.list_tail_ty()
        && caller_spec_key.demand.tuple_field_arity().is_some()
        && fn_can_return_list_tail(m, cont.fn_id)
    {
        return ReturnDemand::list_tail(tail_ty.clone());
    }

    let tuple_demand = tuple_return_demand_for_call(m, *callee, cont);
    if let Some(arity) = tuple_demand.tuple_field_arity()
        && let Some(tail_ty) = caller_spec_key.demand.list_tail_ty()
        && fn_can_return_list_tail(m, cont.fn_id)
    {
        ReturnDemand::tuple_fields_list_tail(arity, tail_ty.clone())
    } else {
        tuple_demand
    }
}

pub(crate) fn continuation_empty_tail_plan<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &Module,
    caller_spec_key: &SpecKey,
    cont: &crate::fz_ir::Cont,
    source: &ContSource,
    demand: &ReturnDemand,
    entry_key: &SpecKey,
) -> Option<ReturnContextPlan> {
    if !caller_spec_key.demand.is_value()
        || !matches!(source, ContSource::Call { .. })
        || !fn_can_return_list_tail(m, cont.fn_id)
    {
        return None;
    }
    let arity = demand.tuple_field_arity()?;
    let any = t.any();
    let tail_ty = t.list(any);
    let mut target = entry_key.clone();
    target.demand = ReturnDemand::tuple_fields_list_tail(arity, tail_ty.clone());
    Some(ReturnContextPlan::ContinuationEmptyTail {
        continuation: cont.fn_id,
        target,
        tail_ty,
    })
}

fn direct_call_return_context_plan(
    m: &Module,
    caller_spec_key: &SpecKey,
    continuation: &crate::fz_ir::Cont,
    demand: &ReturnDemand,
) -> Option<ReturnContextPlan> {
    let tail_ty = demand.list_tail_ty()?.clone();
    if caller_spec_key.demand.tuple_field_arity().is_some()
        && caller_spec_key.demand.list_tail_ty().is_some()
    {
        let mut captures = continuation.captured.iter().copied();
        let (Some(pivot), Some(tail)) = (captures.next(), captures.next()) else {
            return None;
        };
        return Some(ReturnContextPlan::ContinuationListTailBridge {
            continuation: continuation.fn_id,
            pivot,
            tail,
            tail_ty,
        });
    }

    let cont_fn = m.fn_by_id(continuation.fn_id);
    let result_param = cont_fn.block(cont_fn.entry).params.first().copied()?;
    Some(ReturnContextPlan::DirectContinuation {
        continuation: continuation.fn_id,
        result_param,
        tail_ty,
    })
}

fn tuple_return_demand_for_call(
    m: &Module,
    callee: FnId,
    cont: &crate::fz_ir::Cont,
) -> ReturnDemand {
    let Some(arity) = continuation_tuple_field_arity(m, cont) else {
        return ReturnDemand::value();
    };
    if fn_returns_tuple_fields_without_material_value(m, callee, arity) {
        ReturnDemand::tuple_fields(arity)
    } else {
        ReturnDemand::value()
    }
}

fn return_demand_for_call<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &Module,
    fn_effects: &FnEffects,
    env: &HashMap<Var, crate::types::Ty>,
    callee: FnId,
    cont: &crate::fz_ir::Cont,
) -> ReturnDemand {
    let demand = tuple_return_demand_for_call(m, callee, cont);
    if demand.tuple_field_arity().is_some() {
        return demand;
    }
    let Some(tail_ty) = continuation_list_tail_context(t, m, fn_effects, cont, env) else {
        return ReturnDemand::value();
    };
    if fn_can_return_list_tail(m, callee) {
        ReturnDemand::list_tail(tail_ty)
    } else {
        ReturnDemand::value()
    }
}

fn continuation_tuple_field_arity(m: &Module, cont: &crate::fz_ir::Cont) -> Option<usize> {
    let cont_fn = m.fn_by_id(cont.fn_id);
    let entry = cont_fn.block(cont_fn.entry);
    let tuple_param = *entry.params.first()?;
    let mut max_idx: Option<u32> = None;
    let mut seen = HashSet::new();
    let mut tuple_value_used = false;

    for b in &cont_fn.blocks {
        for Stmt::Let(_, prim) in &b.stmts {
            match prim {
                Prim::TupleField(v, idx) if *v == tuple_param => {
                    seen.insert(*idx);
                    max_idx = Some(max_idx.map_or(*idx, |m| m.max(*idx)));
                }
                Prim::TypeTest(v, _) if *v == tuple_param => {}
                other if prim_uses_var(other, tuple_param) => tuple_value_used = true,
                _ => {}
            }
        }
        if term_uses_var(&b.terminator, tuple_param) {
            tuple_value_used = true;
        }
    }
    if tuple_value_used {
        return None;
    }
    let arity = max_idx? as usize + 1;
    if arity == 0 || seen.len() != arity {
        return None;
    }
    Some(arity)
}

fn fn_returns_tuple_fields_without_material_value(m: &Module, fn_id: FnId, arity: usize) -> bool {
    fn go(m: &Module, fn_id: FnId, arity: usize, visiting: &mut HashSet<FnId>) -> bool {
        if !visiting.insert(fn_id) {
            return true;
        }
        let f = m.fn_by_id(fn_id);
        let mut returned = false;
        for b in &f.blocks {
            match &b.terminator {
                Term::Return(v) => {
                    returned = true;
                    if !return_var_is_tuple_arity(b, *v, arity) {
                        return false;
                    }
                }
                Term::TailCall { callee, .. } if go(m, *callee, arity, visiting) => {}
                Term::Goto(_, _) | Term::If { .. } | Term::Halt(_) => {}
                _ => return false,
            }
        }
        visiting.remove(&fn_id);
        returned
            || f.blocks
                .iter()
                .any(|b| matches!(b.terminator, Term::TailCall { .. }))
    }
    go(m, fn_id, arity, &mut HashSet::new())
}

fn continuation_list_tail_context<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &Module,
    fn_effects: &FnEffects,
    cont: &crate::fz_ir::Cont,
    caller_env: &HashMap<Var, crate::types::Ty>,
) -> Option<crate::types::Ty> {
    let cont_fn = m.fn_by_id(cont.fn_id);
    let entry = cont_fn.block(cont_fn.entry);
    let result_param = *entry.params.first()?;
    list_tail_context_for_hole(
        t,
        m,
        fn_effects,
        cont.fn_id,
        result_param,
        Some(caller_env),
        &mut HashSet::new(),
    )
}

fn list_tail_context_for_hole<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    m: &Module,
    fn_effects: &FnEffects,
    fn_id: FnId,
    hole: Var,
    local_env: Option<&HashMap<Var, crate::types::Ty>>,
    visiting: &mut HashSet<(FnId, Var)>,
) -> Option<crate::types::Ty> {
    if !visiting.insert((fn_id, hole)) {
        let any = t.any();
        return Some(t.list(any));
    }
    let f = m.fn_by_id(fn_id);
    if fn_blocks_return_context_motion(fn_effects, fn_id) {
        visiting.remove(&(fn_id, hole));
        return None;
    }
    let mut found = None;
    for b in &f.blocks {
        for Stmt::Let(_, prim) in &b.stmts {
            if prim_uses_var(prim, hole) {
                visiting.remove(&(fn_id, hole));
                return None;
            }
        }
        match &b.terminator {
            Term::TailCall { callee, args, .. }
                if args.first().copied() == Some(hole) && args.len() >= 2 =>
            {
                if !fn_can_return_list_tail(m, *callee) {
                    visiting.remove(&(fn_id, hole));
                    return None;
                }
                found = Some(list_tail_ty_for_var(t, local_env, args[1]));
            }
            Term::Call {
                args, continuation, ..
            } if !args.contains(&hole) => {
                let Some(capture_idx) = continuation.captured.iter().position(|v| *v == hole)
                else {
                    continue;
                };
                let next_fn = m.fn_by_id(continuation.fn_id);
                let next_entry = next_fn.block(next_fn.entry);
                let next_hole = *next_entry.params.get(capture_idx + 1)?;
                let next = list_tail_context_for_hole(
                    t,
                    m,
                    fn_effects,
                    continuation.fn_id,
                    next_hole,
                    None,
                    visiting,
                )?;
                found = Some(next);
            }
            term if term_uses_var(term, hole) => {
                visiting.remove(&(fn_id, hole));
                return None;
            }
            _ => {}
        }
    }
    visiting.remove(&(fn_id, hole));
    found
}

/// Does executing `fn_id` perform — or reach through its call graph — any
/// operation that could observe or be disturbed by relocating an allocation
/// between building a cons cell and filling its tail? Read from the cached
/// per-FnId fact (`compute_fn_effects`); an absent entry is treated as the
/// conservative blocking default.
fn fn_blocks_return_context_motion(fn_effects: &FnEffects, fn_id: FnId) -> bool {
    fn_effects
        .get(&fn_id)
        .copied()
        .unwrap_or_default()
        .blocks_return_context_motion()
}

fn cons_then_direct_list_tail_plan(
    m: &Module,
    caller_spec_key: &SpecKey,
    callee: FnId,
    args: &[Var],
    continuation: &crate::fz_ir::Cont,
) -> Option<(Var, Var, crate::types::Ty)> {
    let tail_ty = caller_spec_key.demand.list_tail_ty()?.clone();
    if args.len() != 1 || !fn_can_return_list_tail(m, callee) {
        return None;
    }
    let caller_fn = m.fn_by_id(caller_spec_key.fn_id);
    let caller_entry = caller_fn.block(caller_fn.entry);
    let mut captures = continuation.captured.iter().copied();
    let pivot = captures.next()?;
    let tail = captures.next()?;
    (caller_entry.params.first().copied() == Some(tail)).then_some((pivot, tail, tail_ty))
}

fn list_tail_ty_for_var<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    local_env: Option<&HashMap<Var, crate::types::Ty>>,
    var: Var,
) -> crate::types::Ty {
    if let Some(ty) = local_env.and_then(|env| env.get(&var)).cloned() {
        return ty;
    }
    let any = t.any();
    t.list(any)
}

fn fn_can_return_list_tail(m: &Module, fn_id: FnId) -> bool {
    fn go(m: &Module, fn_id: FnId, visiting: &mut HashSet<FnId>) -> bool {
        if !visiting.insert(fn_id) {
            return true;
        }
        let f = m.fn_by_id(fn_id);
        let mut saw_return_or_tail = false;
        for b in &f.blocks {
            match &b.terminator {
                Term::Return(v) => {
                    saw_return_or_tail = true;
                    if !return_var_is_list_material(f, b, *v) {
                        visiting.remove(&fn_id);
                        return false;
                    }
                }
                Term::TailCall { callee, .. } => {
                    saw_return_or_tail = true;
                    if !go(m, *callee, visiting) {
                        visiting.remove(&fn_id);
                        return false;
                    }
                }
                Term::Call { continuation, .. } => {
                    saw_return_or_tail = true;
                    if !go(m, continuation.fn_id, visiting) {
                        visiting.remove(&fn_id);
                        return false;
                    }
                }
                Term::Goto(_, _) | Term::If { .. } | Term::Halt(_) => {}
                _ => {
                    visiting.remove(&fn_id);
                    return false;
                }
            }
        }
        visiting.remove(&fn_id);
        saw_return_or_tail
    }
    go(m, fn_id, &mut HashSet::new())
}

fn return_var_is_list_material(f: &FnIr, b: &crate::fz_ir::Block, ret: Var) -> bool {
    if f.block(f.entry).params.contains(&ret) {
        return true;
    }
    for Stmt::Let(dst, prim) in b.stmts.iter().rev() {
        if *dst != ret {
            continue;
        }
        return matches!(
            prim,
            Prim::MakeList(_, _) | Prim::DestListFreeze { .. } | Prim::ListTail(_)
        );
    }
    false
}

fn return_var_is_tuple_arity(b: &crate::fz_ir::Block, ret: Var, arity: usize) -> bool {
    for Stmt::Let(dst, prim) in b.stmts.iter().rev() {
        if *dst != ret {
            continue;
        }
        return match prim {
            Prim::MakeTuple(elems) => elems.len() == arity,
            Prim::DestFreeze { dest, .. } => b.stmts.iter().any(|Stmt::Let(v, p)| {
                *v == *dest && matches!(p, Prim::DestTupleBegin { arity: a, .. } if *a == arity)
            }),
            _ => false,
        };
    }
    false
}
