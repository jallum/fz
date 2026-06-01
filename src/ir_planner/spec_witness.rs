use super::fn_types::{
    FixedPointSlotSummaries, ReturnDemand, SpecKey, SpecKeySet, fixed_point_spec_key_for_arity,
};
use crate::fz_ir::{FnId, Module};
use crate::specs::{
    CallbackReturnDemand, CallbackReturnFact, CallbackReturnQuery, ResolvedSpecSet,
    SpecApplicationOutcome, apply_spec_set,
};
use crate::types::{ClosureTypes, Ty, Types};
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
    let outcome = apply_spec_set(t, spec_set, arg_tys, |t, query: CallbackReturnQuery<'_>| {
        callback_return_fact(
            t,
            module,
            recursive_fns,
            slot_summaries,
            caller,
            effective_returns,
            complete_returns,
            query,
        )
    });
    match outcome {
        SpecApplicationOutcome::Known(application) => Some(DeclaredReturnFact {
            ty: application.result,
            complete: application.complete,
            reads: application.reads,
        }),
        SpecApplicationOutcome::Underconstrained(application) => {
            application.partial_result.map(|ty| DeclaredReturnFact {
                ty,
                complete: false,
                reads: application.reads,
            })
        }
        SpecApplicationOutcome::NoMatch => None,
    }
}

#[allow(clippy::too_many_arguments)]
fn callback_return_fact<T>(
    t: &mut T,
    module: &Module,
    recursive_fns: &std::collections::HashSet<FnId>,
    slot_summaries: &FixedPointSlotSummaries,
    caller: FnId,
    effective_returns: &HashMap<SpecKey, Ty>,
    complete_returns: Option<&SpecKeySet>,
    query: CallbackReturnQuery<'_>,
) -> Option<CallbackReturnFact<SpecKey>>
where
    T: Types<Ty = Ty> + ClosureTypes,
{
    let fn_id: FnId = query.target.into();
    let target_fn = module.fn_by_id(fn_id);
    let n_params = target_fn.block(target_fn.entry).params.len();
    let mut full_key = query.captures.to_vec();
    full_key.extend_from_slice(query.args);
    let key = fixed_point_spec_key_for_arity(
        t,
        module,
        recursive_fns,
        slot_summaries,
        caller,
        fn_id,
        full_key,
        n_params,
        Some(callback_return_demand(query.demand)),
    );

    let Some(ret) = effective_returns.get(&key).cloned() else {
        return Some(CallbackReturnFact::Pending { read: key });
    };
    if complete_returns.is_some_and(|done| !done.contains(&key)) {
        return Some(CallbackReturnFact::Pending { read: key });
    }
    Some(CallbackReturnFact::Known {
        result: ret,
        read: key,
        complete: true,
    })
}

fn callback_return_demand(demand: CallbackReturnDemand) -> ReturnDemand {
    match demand {
        CallbackReturnDemand::Value => ReturnDemand::value(),
        CallbackReturnDemand::TupleFields(arity) => ReturnDemand::tuple_fields(arity),
    }
}
