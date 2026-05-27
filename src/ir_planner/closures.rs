use super::fn_types::{ModulePlan, SpecKey};
use crate::fz_ir::{FnId, Module, Term, Var};
use std::collections::HashMap;

/// Resolve a closure call's return type for this call site's argument types.
///
/// Translates value-demand `effective_returns` into the closure-target return
/// table expected by `Types::resolve_closure_return`, then delegates.
pub fn resolve_closure_return<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    closure_ty: &crate::types::Ty,
    effective_returns: &HashMap<SpecKey, crate::types::Ty>,
    arg_tys: &[crate::types::Ty],
) -> Option<T::Ty> {
    let translated: HashMap<
        (crate::types::ClosureTarget, Vec<crate::types::Ty>),
        crate::types::Ty,
    > = effective_returns
        .iter()
        .filter_map(|(key, ty)| {
            if !key.demand.is_value() || key.input.iter().any(Option::is_none) {
                return None;
            }
            Some((
                (
                    key.fn_id.into(),
                    crate::types::key_slots_observed(&key.input),
                ),
                ty.clone(),
            ))
        })
        .collect();
    t.resolve_closure_return(closure_ty, &translated, arg_tys)
}

/// Rewrite `Term::CallClosure(v, args, cont)` to `Term::Call(F, args, cont)`
/// (and `TailCallClosure` to `TailCall`) when every spec of the enclosing FnIr
/// that has an opinion on `v` agrees that `v` holds `F`. Disagreement leaves
/// the terminator untouched.
///
/// Module mutation only; callers re-run `plan_module` afterwards to
/// refresh `ModulePlan` against the rewritten IR.
pub fn rewrite_known_target_closures<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    _t: &mut T,
    module: &mut Module,
    types: &ModulePlan,
) {
    let mut unified: HashMap<FnId, HashMap<Var, Option<FnId>>> = HashMap::new();
    for (key, ft) in &types.specs {
        if !key.demand.is_value() {
            continue;
        }
        let entry = unified.entry(key.fn_id).or_default();
        for (v, fnid) in &ft.fn_constants {
            match entry.get(v).copied() {
                None => {
                    entry.insert(*v, Some(*fnid));
                }
                Some(Some(prev)) if prev == *fnid => {}
                Some(_) => {
                    entry.insert(*v, None);
                }
            }
        }
    }
    for f in &mut module.fns {
        let Some(map) = unified.get(&f.id) else {
            continue;
        };
        for b in &mut f.blocks {
            let new_term = match &b.terminator {
                Term::CallClosure {
                    ident: _,
                    closure,
                    args,
                    continuation,
                } => {
                    if let Some(Some(target)) = map.get(closure).copied() {
                        Some(Term::Call {
                            ident: crate::fz_ir::CallsiteIdent::from_source(
                                crate::diag::Span::DUMMY,
                            ),
                            callee: target,
                            args: args.clone(),
                            continuation: continuation.clone(),
                        })
                    } else {
                        None
                    }
                }
                Term::TailCallClosure {
                    closure,
                    args,
                    ident: _,
                } => {
                    if let Some(Some(target)) = map.get(closure).copied() {
                        Some(Term::TailCall {
                            ident: crate::fz_ir::CallsiteIdent::from_source(
                                crate::diag::Span::DUMMY,
                            ),
                            callee: target,
                            args: args.clone(),
                            is_back_edge: false,
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(nt) = new_term {
                b.terminator = nt;
            }
        }
    }
}
