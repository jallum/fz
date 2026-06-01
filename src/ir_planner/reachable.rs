use super::closures::resolve_closure_return;
use super::fn_types::{ModulePlan, SpecKey, SpecPlan, normalize_result_correspondence_key};
use super::type_fn::type_stmts_into_env;
use crate::fz_ir::{Block, Cont, FnId, Module, Prim, Stmt, Term, Var};
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
    let recursive_fns = HashSet::new();
    let effective_returns = HashMap::new();
    super::spec_witness::declared_return_fact(
        t,
        module,
        &recursive_fns,
        &super::fn_types::FixedPointSlotSummaries::new(),
        callee,
        callee,
        arg_tys,
        &effective_returns,
        None,
    )
    .map(|fact| fact.ty)
}

/// Compute the set of SpecIds reachable at runtime from `main` (plus registered
/// closure-target specs as a conservative catch).
///
/// Codegen consults this to skip body emission for unreached specs: a
/// trap stub goes out instead of the full body, dramatically shrinking
/// the emitted binary and the golden CLIF for fixtures that have any
/// per-callsite specialization fan-out the runtime never reaches
/// (ast_eval is the canonical example — pre-prune it ships eval(any),
/// eval(int), eval(2), eval(3), eval(4) bodies that no callsite ever
/// resolves to).
///
/// Algorithm:
///   - Seed with main's spec id, every test/exported entry, and every
///     registered spec whose fn appears in a `MakeClosure` (conservatively
///     covers opaque closure dispatch without needing per-site
///     closure_lit resolution).
///   - BFS: for each reached spec, walk its reachable blocks, find
///     direct Call/TailCall + their conts and CallClosure/TailCallClosure
///     resolvable via known callable capabilities. Use the same `SpecRegistry::resolve`
///     subsumption search codegen uses, so a spec marked reachable here
///     is exactly a spec codegen will look up.
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
        self.seed_closure_target_specs(&mut worklist);
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

    fn seed_closure_target_specs(&self, worklist: &mut Vec<u32>) {
        let closure_target_fns = self.collect_closure_target_fns();
        for (sid, key) in self.spec_registry.iter() {
            if closure_target_fns.contains(&key.fn_id) {
                worklist.push(sid.0);
            }
        }
    }

    fn collect_closure_target_fns(&self) -> HashSet<FnId> {
        let mut closure_target_fns = HashSet::new();
        for f in &self.module.fns {
            for blk in &f.blocks {
                for stmt in &blk.stmts {
                    let Stmt::Let(_, prim) = stmt;
                    if let Prim::MakeClosure(_, lam_id, _) = prim {
                        closure_target_fns.insert(*lam_id);
                    }
                }
            }
        }
        closure_target_fns
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
        let blocks = self.module.fns[j].blocks.clone();
        for blk in &blocks {
            if ft.reachable_blocks.contains(&blk.id) {
                self.enqueue_successors_for_block(&ft, blk, worklist);
            }
        }
    }

    fn enqueue_successors_for_block(
        &mut self,
        ft: &SpecPlan,
        blk: &Block,
        worklist: &mut Vec<u32>,
    ) {
        let env = env_at_terminator(self.t, ft, blk, self.module);
        match &blk.terminator {
            Term::Call {
                callee,
                args,
                continuation,
                ..
            } => {
                self.enqueue_direct_call(*callee, args, &env, worklist);
                self.enqueue_continuation(blk, ft, continuation, worklist);
            }
            Term::TailCall { callee, args, .. } => {
                self.enqueue_direct_call(*callee, args, &env, worklist);
            }
            Term::CallClosure {
                closure,
                args,
                continuation,
                ..
            } => {
                if let Some(target) = ft.known_fn(closure) {
                    self.enqueue_direct_call(target, args, &env, worklist);
                }
                self.enqueue_continuation(blk, ft, continuation, worklist);
            }
            Term::TailCallClosure { closure, args, .. } => {
                if let Some(target) = ft.known_fn(closure) {
                    self.enqueue_direct_call(target, args, &env, worklist);
                }
            }
            Term::Receive { continuation, .. } => {
                self.enqueue_continuation(blk, ft, continuation, worklist);
            }
            Term::ReceiveMatched { clauses, after, .. } => {
                self.enqueue_receive_matched_outcomes(clauses, after, worklist);
            }
            _ => {}
        }
    }

    fn enqueue_direct_call(
        &mut self,
        callee: FnId,
        args: &[Var],
        env: &HashMap<Var, crate::types::Ty>,
        worklist: &mut Vec<u32>,
    ) {
        let any = self.t.any();
        let arg_tys = args
            .iter()
            .map(|av| env.get(av).cloned().unwrap_or_else(|| any.clone()))
            .collect();
        let key = self.pad_to_arity(callee, arg_tys, &any);
        self.enqueue_value_key(callee, key, worklist);
    }

    fn enqueue_continuation(
        &mut self,
        blk: &Block,
        ft: &SpecPlan,
        continuation: &Cont,
        worklist: &mut Vec<u32>,
    ) {
        let cont_key = cont_input_key(self.t, blk, continuation, ft, self.module, self.module_plan);
        self.enqueue_value_key(continuation.fn_id, cont_key, worklist);
    }

    fn enqueue_receive_matched_outcomes(
        &mut self,
        clauses: &[crate::fz_ir::ReceiveClause],
        after: &Option<crate::fz_ir::ReceiveAfter>,
        worklist: &mut Vec<u32>,
    ) {
        let any = self.t.any();
        for c in clauses {
            self.enqueue_receive_outcome(c.body, &any, worklist);
            if let Some(g) = c.guard {
                self.enqueue_receive_outcome(g, &any, worklist);
            }
        }
        if let Some(a) = after {
            self.enqueue_receive_outcome(a.body, &any, worklist);
        }
    }

    fn enqueue_receive_outcome(
        &mut self,
        fid: FnId,
        any: &crate::types::Ty,
        worklist: &mut Vec<u32>,
    ) {
        let Some(&j) = self.module.fn_idx.get(&fid) else {
            return;
        };
        let body = &self.module.fns[j];
        let np = body.block(body.entry).params.len();
        let key = crate::fz_ir::receive_outcome_spec_key(any, np);
        self.enqueue_value_key(fid, key, worklist);
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

    fn pad_to_arity(
        &self,
        callee: FnId,
        mut tys: Vec<crate::types::Ty>,
        any: &crate::types::Ty,
    ) -> Vec<crate::types::Ty> {
        if let Some(&j) = self.module.fn_idx.get(&callee) {
            let np = self.module.fns[j]
                .block(self.module.fns[j].entry)
                .params
                .len();
            while tys.len() < np {
                tys.push(any.clone());
            }
            tys.truncate(np);
        }
        tys
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
