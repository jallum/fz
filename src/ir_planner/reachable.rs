use super::closures::resolve_closure_return;
use super::fn_types::{ModulePlan, SpecKey, SpecPlan, normalize_result_correspondence_key};
use super::type_fn::type_stmts_into_env;
use crate::fz_ir::{
    Block, CallsiteId, CallsiteIdent, Cont, EmitSlot, FnId, FnIr, Module, Prim, Stmt, Term, Var,
};
use std::collections::{HashMap, HashSet};

// Continuation input-type key helpers.

/// Reconstruct the per-Var env at the *terminator* of `block` under
/// `caller_ft`. Starts from `caller_ft.block_envs[block.id]` (which
/// already incorporates if-narrowing from predecessor blocks) and folds in
/// each Let by re-applying `type_prim`.
pub(crate) fn env_at_terminator<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    caller_ft: &SpecPlan,
    block: &Block,
    module: &Module,
) -> HashMap<Var, crate::types::Ty> {
    let mut env: HashMap<Var, crate::types::Ty> = caller_ft
        .block_envs
        .get(&block.id)
        .cloned()
        .unwrap_or_default();
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
pub fn cont_slot0_descr<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    block: &Block,
    caller_ft: &SpecPlan,
    module: &Module,
    module_plan: &ModulePlan,
) -> T::Ty {
    match &block.terminator {
        Term::Call { callee, args, .. } => {
            let env = env_at_terminator(t, caller_ft, block, module);
            let arg_tys: Vec<crate::types::Ty> = args
                .iter()
                .map(|av| env.get(av).cloned().unwrap_or_else(|| t.any()))
                .collect();
            let effective = module_plan
                .effective_return_for_call_ty(t, *callee, &arg_tys)
                .as_ref()
                .cloned();
            let declared = declared_call_return(t, module, *callee, &arg_tys);
            match (declared, effective) {
                (Some(declared), Some(effective)) if t.is_subtype(&effective, &declared) => {
                    effective
                }
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
            if t.closure_lit_parts(&closure_d)
                .is_some_and(|lit| !lit.captures.is_empty())
            {
                let arg_tys: Vec<crate::types::Ty> = args
                    .iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| t.any()))
                    .collect();
                match resolve_closure_return(
                    t,
                    &closure_d,
                    &module_plan.effective_returns,
                    &arg_tys,
                ) {
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

fn declared_call_return<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    callee: FnId,
    arg_tys: &[crate::types::Ty],
) -> Option<crate::types::Ty> {
    let spec_set = module.declared_specs.get(&callee)?;
    match crate::specs::apply_spec_set::<_, (), _>(t, spec_set, arg_tys, |_t, _query| None) {
        crate::specs::SpecApplicationOutcome::Known(application) => Some(application.result),
        crate::specs::SpecApplicationOutcome::Underconstrained(_) => None,
        crate::specs::SpecApplicationOutcome::NoMatch => None,
    }
}

/// Compute the set of SpecIds reachable at runtime from `main`.
///
/// `PlannedProgram` consults this while materializing the codegen-facing plan.
/// Codegen receives the finished reachable set from `PlannedProgram` and does
/// not rediscover semantic reachability.
///
/// Algorithm:
///   - Seed with main's spec id and every extra reachable seed supplied by
///     materialization.
///   - BFS: for each reached spec, walk the surviving callsites in its live
///     body and follow the already-solved local call-edge targets recorded on
///     the `SpecPlan`. Use `SpecRegistry::resolve` subsumption so a reached
///     spec id names the same registered specialization later consumed by
///     materialization and codegen.
pub fn reachable_specs<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    spec_registry: &crate::frontend::spec_registry::SpecRegistry,
    module_plan: &ModulePlan,
    extra_seeds: impl IntoIterator<Item = u32>,
) -> HashSet<u32> {
    let spec_keys: Vec<SpecKey> = spec_registry.iter().map(|(_, key)| key.clone()).collect();
    let mut ctx = ReachableSpecTraversal {
        t,
        module,
        spec_registry,
        module_plan,
        spec_keys,
    };
    let mut reached = HashSet::new();
    let mut worklist = ctx.seed_specs(extra_seeds);
    while let Some(sid) = worklist.pop() {
        if !reached.insert(sid) {
            continue;
        }
        ctx.enqueue_reachable_successors(sid, &mut worklist);
    }
    reached
}

struct ReachableSpecTraversal<'a, T>
where
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
{
    t: &'a mut T,
    module: &'a Module,
    spec_registry: &'a crate::frontend::spec_registry::SpecRegistry,
    module_plan: &'a ModulePlan,
    spec_keys: Vec<SpecKey>,
}

impl<T> ReachableSpecTraversal<'_, T>
where
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
{
    fn seed_specs(&mut self, extra_seeds: impl IntoIterator<Item = u32>) -> Vec<u32> {
        let mut worklist = Vec::new();
        self.seed_main_spec(&mut worklist);
        worklist.extend(extra_seeds);
        worklist
    }

    fn seed_main_spec(&mut self, worklist: &mut Vec<u32>) {
        let Some(main_fn) = self.module.fns.iter().find(|f| f.name == "main") else {
            return;
        };
        let n_params = main_fn.block(main_fn.entry).params.len();
        let any = self.t.any();
        let key = self.t.repeat(any, n_params);
        self.enqueue_value_key(main_fn.id, key, worklist);
    }

    fn enqueue_reachable_successors(&mut self, sid: u32, worklist: &mut Vec<u32>) {
        let Some(key) = self.spec_keys.get(sid as usize).cloned() else {
            return;
        };
        let Some(ft) = self.module_plan.specs.get(&key).cloned() else {
            return;
        };
        let Some(&j) = self.module.fn_idx.get(&key.fn_id) else {
            return;
        };
        let body = &self.module.fns[j];
        each_local_successor_key(body, &ft, |target| {
            if let Some(sid) = self.spec_registry.resolve_spec_key(self.t, target) {
                worklist.push(sid.0);
            }
        });
    }

    fn enqueue_value_key(
        &mut self,
        fid: FnId,
        tys: Vec<crate::types::Ty>,
        worklist: &mut Vec<u32>,
    ) {
        let key = SpecKey::value(fid, crate::types::key_slots_from_tys(tys));
        if let Some(sid) = self.spec_registry.resolve_spec_key(self.t, &key) {
            worklist.push(sid.0);
        }
    }
}

pub(crate) fn each_local_successor_key(
    body: &FnIr,
    ft: &SpecPlan,
    mut visit: impl FnMut(&SpecKey),
) {
    let mut visit_slot = |ident: &CallsiteIdent, slot: EmitSlot| {
        let callsite = CallsiteId::new(body.id, ident, slot);
        if let Some(target) = ft.local_call_target(&callsite) {
            visit(target);
        }
    };

    for blk in &body.blocks {
        if !ft.reachable_blocks.contains(&blk.id) {
            continue;
        }
        for Stmt::Let(_, prim) in &blk.stmts {
            if let Prim::Extern(ident, _, _) = prim {
                visit_slot(ident, EmitSlot::CallableBoundary);
            }
        }

        match &blk.terminator {
            Term::Call { ident, .. } => {
                visit_slot(ident, EmitSlot::Direct);
                visit_slot(ident, EmitSlot::Cont);
                visit_slot(ident, EmitSlot::CallableBoundary);
            }
            Term::TailCall { ident, .. } => {
                visit_slot(ident, EmitSlot::Direct);
                visit_slot(ident, EmitSlot::CallableBoundary);
            }
            Term::CallClosure { ident, .. } => {
                visit_slot(ident, EmitSlot::ClosureCall);
                visit_slot(ident, EmitSlot::Cont);
            }
            Term::TailCallClosure { ident, .. } => {
                visit_slot(ident, EmitSlot::ClosureCall);
            }
            Term::Receive { ident, .. } => {
                visit_slot(ident, EmitSlot::Cont);
            }
            Term::ReceiveMatched { clauses, after, .. } => {
                for clause in clauses {
                    let ident = CallsiteIdent::from_source(clause.span);
                    visit_slot(&ident, EmitSlot::Cont);
                    if clause.guard.is_some() {
                        let ident = CallsiteIdent::from_source(clause.span);
                        visit_slot(&ident, EmitSlot::Cont);
                    }
                }
                if let Some(after) = after {
                    let ident = CallsiteIdent::from_source(after.span);
                    visit_slot(&ident, EmitSlot::Cont);
                }
            }
            Term::Goto(_, _) | Term::Return(_) | Term::Halt(_) | Term::If { .. } => {}
        }
    }
}

/// Build the full Cont input-type key at a call-site:
/// `[slot0, ...captured_tys]`, padded with `any` to the cont fn's entry-block
/// arity.
pub fn cont_input_key<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    block: &Block,
    continuation: &Cont,
    caller_ft: &SpecPlan,
    module: &Module,
    module_plan: &ModulePlan,
) -> Vec<crate::types::Ty> {
    let cont_fn = module.fn_by_id(continuation.fn_id);
    let n_params = cont_fn.block(cont_fn.entry).params.len();
    let any_t = t.any();
    let env = env_at_terminator(t, caller_ft, block, module);
    let slot0_ty = cont_slot0_descr(t, block, caller_ft, module, module_plan);
    normalize_result_correspondence_key(
        t,
        module,
        continuation.fn_id,
        cont_key_from_slot0(&any_t, n_params, slot0_ty, &continuation.captured, &env),
    )
}

pub(crate) fn cont_key_from_slot0(
    any_t: &crate::types::Ty,
    n_params: usize,
    slot0: crate::types::Ty,
    captured: &[Var],
    env: &HashMap<Var, crate::types::Ty>,
) -> Vec<crate::types::Ty> {
    let mut key: Vec<crate::types::Ty> = vec![any_t.clone(); n_params];
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
