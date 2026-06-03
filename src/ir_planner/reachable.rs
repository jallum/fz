use super::closures::resolve_closure_return;
use super::fn_types::{ModulePlan, SpecPlan};
use super::type_fn::type_stmts_into_env;
use crate::frontend::spec_registry::SpecRegistry;
use crate::fz_ir::{Block, Cont, FnId, Module, Term, Var};
use crate::specs::{SpecApplicationOutcome, apply_spec_set};
use crate::types::{ClosureTypes, Ty, Types};
use std::collections::{HashMap, HashSet};

// Continuation input-type key helpers.

/// Reconstruct the per-Var env at the *terminator* of `block` under
/// `caller_ft`. Starts from `caller_ft.block_envs[block.id]` (which
/// already incorporates if-narrowing from predecessor blocks) and folds in
/// each Let by re-applying `type_prim`.
pub(crate) fn env_at_terminator<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    caller_ft: &SpecPlan,
    block: &Block,
    module: &Module,
) -> HashMap<Var, Ty> {
    let mut env: HashMap<Var, Ty> = caller_ft.block_envs.get(&block.id).cloned().unwrap_or_default();
    type_stmts_into_env(t, &mut env, &block.stmts, module);
    env
}

/// Slot-0 type for a Cont's input-type key at the call-site whose terminator is
/// `block.terminator`:
///
///   * `Term::Call`: callee's effective return under a registered spec that
///     covers this call-site's arg types.
///   * `Term::CallClosure`: closure return resolved from the closure type and
///     registered effective returns, falling back to the structural arrow
///     return.
///   * `Term::Receive`: `any()`.
///   * Anything else: not a Cont-producing terminator, returns `any`.
pub fn cont_slot0_descr<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    block: &Block,
    caller_ft: &SpecPlan,
    module: &Module,
    module_plan: &ModulePlan,
) -> T::Ty {
    match &block.terminator {
        Term::Call { callee, args, .. } => {
            let env = env_at_terminator(t, caller_ft, block, module);
            let arg_tys: Vec<Ty> = args
                .iter()
                .map(|av| env.get(av).cloned().unwrap_or_else(|| t.any()))
                .collect();
            let effective = module_plan
                .effective_return_for_call_ty(t, *callee, &arg_tys)
                .as_ref()
                .cloned();
            let declared = declared_call_return(t, module, *callee, &arg_tys);
            match (declared, effective) {
                (Some(declared), Some(effective)) if t.is_subtype(&effective, &declared) => effective,
                (Some(declared), _) => declared,
                (None, Some(effective)) => effective,
                (None, None) => t.any(),
            }
        }
        // The closure type names the body's possible return shapes. For
        // singleton closure-lits, resolve against the registered body spec;
        // otherwise fall back to the structural arrow-return join.
        Term::CallClosure { closure, args, .. } => {
            let env = env_at_terminator(t, caller_ft, block, module);
            let closure_d = env.get(closure).cloned().unwrap_or_else(|| t.any());
            if t.closure_lit_parts(&closure_d).is_some() {
                let arg_tys: Vec<Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| t.any()))
                    .collect();
                match resolve_closure_return(t, &closure_d, &module_plan.effective_returns, &arg_tys) {
                    Some(ty) => ty,
                    None => t.arrow_join_return(&closure_d),
                }
            } else {
                t.arrow_join_return(&closure_d)
            }
        }
        _ => t.any(),
    }
}

fn declared_call_return<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    callee: FnId,
    arg_tys: &[Ty],
) -> Option<Ty> {
    let spec_set = module.declared_specs.get(&callee)?;
    match apply_spec_set::<_, (), _>(t, spec_set, arg_tys, |_t, _query| None) {
        SpecApplicationOutcome::Known(application) => Some(application.result),
        SpecApplicationOutcome::Underconstrained(_) => None,
        SpecApplicationOutcome::NoMatch => None,
    }
}

/// Resolve the planner's closed reachable `SpecKey` set to stable `SpecId`s.
///
/// `ModulePlan` is already the semantic reachability authority. Materialization
/// and codegen consume those exact specs through the `SpecRegistry`; they do
/// not replay the call graph.
pub fn reachable_spec_ids<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    spec_registry: &SpecRegistry,
    module_plan: &ModulePlan,
) -> HashSet<u32> {
    module_plan
        .reachable_specs
        .iter()
        .map(|key| {
            spec_registry
                .resolve_spec_key(t, key)
                .unwrap_or_else(|| panic!("reachable spec {:?} missing from spec registry", key))
                .0
        })
        .collect()
}

/// Build the full Cont input-type key at a call-site:
/// `[slot0, ...captured_tys]`, padded with `any` to the cont fn's entry-block
/// arity.
pub fn cont_input_key<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    block: &Block,
    continuation: &Cont,
    caller_ft: &SpecPlan,
    module: &Module,
    module_plan: &ModulePlan,
) -> Vec<Ty> {
    let cont_fn = module.fn_by_id(continuation.fn_id);
    let n_params = cont_fn.block(cont_fn.entry).params.len();
    let any_t = t.any();
    let env = env_at_terminator(t, caller_ft, block, module);
    let slot0_ty = cont_slot0_descr(t, block, caller_ft, module, module_plan);
    cont_key_from_slot0(&any_t, n_params, slot0_ty, &continuation.captured, &env)
}

pub(crate) fn cont_key_from_slot0(
    any_t: &Ty,
    n_params: usize,
    slot0: Ty,
    captured: &[Var],
    env: &HashMap<Var, Ty>,
) -> Vec<Ty> {
    let mut key: Vec<Ty> = vec![any_t.clone(); n_params];
    if let Some(first) = key.first_mut() {
        *first = slot0;
    }
    for (k, cv) in captured.iter().enumerate() {
        if let Some(p) = key.get_mut(k + 1) {
            *p = env.get(cv).cloned().unwrap_or_else(|| any_t.clone());
        }
    }
    key
}
