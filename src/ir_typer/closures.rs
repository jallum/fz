use super::fn_types::{ModuleTypes, SpecKey};
use crate::fz_ir::{FnId, Module, Term, Var};
use std::collections::HashMap;

/// fz-ul4.27.22.9 — closure-aware return resolution. Given a closure
/// Var's type and the actual `arg_tys` at a call site, compute the
/// joined return type.
///
/// For each positive arrow clause in `closure_descr.funcs`:
///   - If the clause carries a `ClosureLit { fn_id, captures }`, build the
///     full body key `[captures..., arg_tys...]` and look up
///     `effective_returns[(fn_id, full_key)]`. JOIN into the accumulator.
///   - Otherwise, JOIN `sig.ret` (the existing `arrow_join_return` path).
///
/// Returns `None` when a lit-tagged clause's spec has not yet been
/// registered — caller treats this as a fixpoint deferral (same convention
/// as `cont_slot0_descr` today). Returns `Some(any())` for
/// pathological inputs (empty funcs, negated arrows, saturated `Conj::top`
/// pos clauses) — those convey no narrowing information so the broadest
/// result is sound.
///
/// `arg_tys` length must match the closure's apparent arity for lit
/// clauses; mismatch falls back to `any()` for that clause.
#[allow(dead_code)] // Wired into cont_slot0_descr / codegen in fz-ul4.27.22.10/11.
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

/// fz-ul4.29.10.3 — rewrite `Term::CallClosure(v, args, cont)` →
/// `Term::Call(F, args, cont)` (and `TailCallClosure` → `TailCall`)
/// when `types.specs[..].fn_constants[v] = F` agrees across every spec
/// of the enclosing FnIr that has an opinion on `v`. Disagreement
/// (different specs of the same fn body see different FnIds for the
/// same Var) leaves the terminator untouched — safe fallback.
///
/// Module mutation only; callers re-run `type_module` afterwards to
/// refresh `ModuleTypes` against the rewritten IR (so the typed-spec
/// landscape reflects direct dispatch and `.29.12.6` can drop dead
/// any-keys).
pub fn rewrite_known_target_closures<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    // fz-mm2.6 — verified: body has no concrete representation operations. The seam handle
    // is preserved on the signature so the function stays uniform with
    // its siblings; if a future concrete op lands here, it routes through t.
    _t: &mut T,
    module: &mut Module,
    types: &ModuleTypes,
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
