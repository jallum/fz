use super::fn_types::{
    FixedPointSlotSummaries, ReturnDemand, SpecKey, SpecKeySet, fixed_point_spec_key_for_arity,
};
use crate::fz_ir::{FnId, Module};
use crate::type_expr::{ResolvedSpec, ResolvedSpecSet};
use crate::types::{
    ClosureLitInfo, ClosureTypes, SchemeInstantiation, SchemeMatch, Ty, Types,
    instantiate_scheme_match,
};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub(crate) struct DeclaredReturnFact {
    pub ty: Ty,
    pub complete: bool,
    pub reads: Vec<SpecKey>,
}

pub(crate) fn declared_return_fact<T>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &FixedPointSlotSummaries,
    caller: FnId,
    callee: FnId,
    arg_tys: &[Ty],
    effective_returns: &HashMap<SpecKey, Ty>,
    complete_returns: Option<&SpecKeySet>,
) -> Option<DeclaredReturnFact>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let spec_set = module.declared_specs.get(&callee)?;
    declared_return_fact_from_set(
        t,
        module,
        recursive_fns,
        slot_summaries,
        caller,
        spec_set,
        arg_tys,
        effective_returns,
        complete_returns,
    )
}

pub(crate) fn declared_return_fact_from_set<T>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &FixedPointSlotSummaries,
    caller: FnId,
    spec_set: &ResolvedSpecSet,
    arg_tys: &[Ty],
    effective_returns: &HashMap<SpecKey, Ty>,
    complete_returns: Option<&SpecKeySet>,
) -> Option<DeclaredReturnFact>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let mut result = t.none();
    let mut complete = true;
    let mut reads = Vec::new();
    let mut matched_any = false;

    for spec in &spec_set.arrows {
        let Some(fact) = declared_return_fact_for_arrow(
            t,
            module,
            recursive_fns,
            slot_summaries,
            caller,
            spec,
            arg_tys,
            effective_returns,
            complete_returns,
        ) else {
            continue;
        };
        matched_any = true;
        complete &= fact.complete;
        reads.extend(fact.reads);
        result = t.union(result, fact.ty);
    }

    matched_any.then_some(DeclaredReturnFact {
        ty: result,
        complete,
        reads,
    })
}

fn declared_return_fact_for_arrow<T>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &FixedPointSlotSummaries,
    caller: FnId,
    spec: &ResolvedSpec,
    arg_tys: &[Ty],
    effective_returns: &HashMap<SpecKey, Ty>,
    complete_returns: Option<&SpecKeySet>,
) -> Option<DeclaredReturnFact>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let first =
        match instantiate_scheme_match(t, &spec.params, &spec.result, &spec.constraints, arg_tys) {
            SchemeInstantiation::Known(matched)
            | SchemeInstantiation::Underconstrained(matched) => matched,
            SchemeInstantiation::Invalid => return None,
        };

    let mut refined_witnesses = arg_tys.to_vec();
    let mut complete = true;
    let mut reads = Vec::new();
    for (slot, ((pattern, matched_param), witness)) in spec
        .params
        .iter()
        .zip(first.params.iter())
        .zip(arg_tys.iter())
        .enumerate()
    {
        let Some(refined) = higher_order_witness(
            t,
            module,
            recursive_fns,
            slot_summaries,
            caller,
            pattern,
            matched_param,
            witness,
            effective_returns,
            complete_returns,
            &mut reads,
            &mut complete,
        ) else {
            continue;
        };
        // Keep the closure-literal identity and add the resolved arrow
        // evidence. Replacing the witness would turn a closure value into a
        // narrower callable contract and make function subtyping reject the
        // widened accumulator.
        refined_witnesses[slot] = t.union(witness.clone(), refined);
    }

    let matched = match instantiate_scheme_match(
        t,
        &spec.params,
        &spec.result,
        &spec.constraints,
        &refined_witnesses,
    ) {
        SchemeInstantiation::Known(SchemeMatch { result, .. })
        | SchemeInstantiation::Underconstrained(SchemeMatch { result, .. }) => result,
        SchemeInstantiation::Invalid => return None,
    };

    Some(DeclaredReturnFact {
        ty: matched,
        complete,
        reads,
    })
}

#[allow(clippy::too_many_arguments)]
fn higher_order_witness<T>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &FixedPointSlotSummaries,
    caller: FnId,
    pattern: &Ty,
    matched_param: &Ty,
    witness: &Ty,
    effective_returns: &HashMap<SpecKey, Ty>,
    complete_returns: Option<&SpecKeySet>,
    reads: &mut Vec<SpecKey>,
    complete: &mut bool,
) -> Option<Ty>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let pattern_clauses = t.callable_clauses(pattern)?;
    if !pattern_clauses.iter().any(|clause| t.has_vars(&clause.ret)) {
        return None;
    }
    let matched_clauses = t.callable_clauses(matched_param)?;
    let witness_clauses = t.callable_clauses(witness)?;
    let closure_lits = witness_clauses
        .into_iter()
        .filter_map(|clause| clause.closure)
        .collect::<Vec<_>>();
    if closure_lits.is_empty() {
        return None;
    }

    let mut refined = t.none();
    let mut saw_clause = false;
    for matched_clause in matched_clauses {
        let demand = demand_for_callable_result(t, &matched_clause.ret);
        for ClosureLitInfo { target, captures } in &closure_lits {
            let fn_id: FnId = (*target).into();
            let target_fn = module.fn_by_id(fn_id);
            let n_params = target_fn.block(target_fn.entry).params.len();
            let mut full_key = captures.clone();
            full_key.extend(matched_clause.args.clone());
            let key = fixed_point_spec_key_for_arity(
                t,
                module,
                recursive_fns,
                slot_summaries,
                caller,
                fn_id,
                full_key,
                n_params,
                Some(demand.clone()),
            );
            reads.push(key.clone());
            let Some(ret) = effective_returns.get(&key).cloned() else {
                *complete = false;
                continue;
            };
            if complete_returns.is_some_and(|done| !done.contains(&key)) {
                *complete = false;
                continue;
            }
            let arrow = t.arrow(&matched_clause.args, ret);
            refined = t.union(refined, arrow);
            saw_clause = true;
        }
    }

    saw_clause.then_some(refined)
}

fn demand_for_callable_result<T>(t: &T, result: &Ty) -> ReturnDemand
where
    T: Types<Ty = Ty>,
{
    let arity = t.max_tuple_arity(result);
    if arity > 0 {
        ReturnDemand::tuple_fields(arity)
    } else {
        ReturnDemand::value()
    }
}
