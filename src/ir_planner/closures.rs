use super::fn_types::{BodyKey, ReturnDemand, SpecKey, fixed_point_spec_key_for_arity};
use crate::fz_ir::{FnId, Module};
use crate::types::{CallableClause, ClosureTarget, ClosureTypes, Ty, Types, key_slots_observed};
use std::collections::{HashMap, HashSet};

/// Resolve a closure call's return type for this call site's argument types.
///
/// Translates value-demand `effective_returns` into the closure-target return
/// table expected by the specs matcher, then delegates.
pub fn resolve_closure_return<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    closure_ty: &Ty,
    effective_returns: &HashMap<BodyKey, Ty>,
    arg_tys: &[Ty],
) -> Option<T::Ty> {
    let translated: HashMap<(ClosureTarget, Vec<Ty>), Ty> = effective_returns
        .iter()
        .filter_map(|(key, ty)| {
            if key.input.iter().any(Option::is_none) {
                return None;
            }
            Some(((key.fn_id.into(), key_slots_observed(&key.input)), ty.clone()))
        })
        .collect();
    crate::specs::resolve_closure_return(t, closure_ty, &translated, arg_tys)
}

pub fn literal_closure_return_keys<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    recursive_fns: &HashSet<FnId>,
    caller: FnId,
    closure_ty: &Ty,
    arg_tys: &[Ty],
    demand: Option<ReturnDemand>,
) -> Option<Vec<SpecKey>> {
    let clauses = t.callable_clauses(closure_ty)?;
    let mut keys = Vec::new();
    for clause in clauses {
        let CallableClause {
            args,
            closure: Some(closure),
            ..
        } = clause
        else {
            return None;
        };
        if args.len() != arg_tys.len() {
            continue;
        }
        let fn_id: FnId = closure.target.into();
        let target_fn = module.fn_by_id(fn_id);
        let n_params = target_fn.block(target_fn.entry).params.len();
        let mut full_key = closure.captures;
        full_key.extend_from_slice(arg_tys);
        keys.push(fixed_point_spec_key_for_arity(
            t,
            module,
            recursive_fns,
            caller,
            fn_id,
            full_key,
            n_params,
            demand.clone(),
        ));
    }
    Some(keys)
}
