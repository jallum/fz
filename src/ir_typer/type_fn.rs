use super::expr_types::{lookup, var_as_map_key};
use super::fn_types::FnTypes;
use super::narrow::{find_emptied_var, merge_into, narrow_for_if};
use super::prim::type_prim;
use crate::fz_ir::{BlockId, FnId, FnIr, InitTokenId, Module, Prim, Stmt, Term, Var};
use crate::ir_dest::{
    TokenState, TupleDestState, begin_tuple_dest, consume_init_token, define_init_token,
    freeze_tuple_dest, set_tuple_dest_field,
};
use std::collections::{HashMap, HashSet};

/// BFS from entry; returns blocks in topological order for all forward edges.
/// Back-edges (to already-visited blocks) are skipped — the outer fixpoint
/// in `type_fn` handles them by iterating until convergence.
/// Unreachable blocks (dead-code match-error branches etc.) are appended
/// after the reachable prefix so their vars still get typed.
pub(crate) fn topo_order(f: &FnIr) -> Vec<BlockId> {
    let mut visited: HashSet<BlockId> = HashSet::new();
    let mut order: Vec<BlockId> = Vec::with_capacity(f.blocks.len());
    let mut queue: std::collections::VecDeque<BlockId> = std::collections::VecDeque::new();
    queue.push_back(f.entry);
    visited.insert(f.entry);
    while let Some(bid) = queue.pop_front() {
        order.push(bid);
        let b = f.block(bid);
        let if_pair;
        let succs: &[BlockId] = match &b.terminator {
            Term::Goto(t, _) => std::slice::from_ref(t),
            Term::If { then_b, else_b, .. } => {
                if_pair = [*then_b, *else_b];
                &if_pair
            }
            _ => &[],
        };
        for &s in succs {
            if visited.insert(s) {
                queue.push_back(s);
            }
        }
    }
    // Append unreachable blocks so their vars are still typed.
    for b in &f.blocks {
        if visited.insert(b.id) {
            order.push(b.id);
        }
    }
    order
}

fn type_let_with_init_facts<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    result: Var,
    prim: &Prim,
    env: &HashMap<Var, crate::types::Ty>,
    m: &Module,
    const_vars: &HashSet<Var>,
    init_tokens: &mut HashMap<InitTokenId, TokenState>,
    tuple_dests: &mut HashMap<Var, TupleDestState<crate::types::Ty>>,
    list_builders: &mut HashMap<InitTokenId, crate::types::Ty>,
    map_dests: &mut HashMap<InitTokenId, crate::types::Ty>,
) -> crate::types::Ty {
    match prim {
        Prim::DestTupleBegin { token, arity } => {
            let _ = define_init_token(init_tokens, *token);
            begin_tuple_dest(tuple_dests, result, *arity);
            t.any()
        }
        Prim::DestTupleSet {
            dest,
            token,
            index,
            value,
            next,
        } => {
            if consume_init_token(init_tokens, *token).is_ok() {
                let next_ok = define_init_token(init_tokens, *next).is_ok();
                let value_ty = lookup(t, env, *value);
                let set_ok = set_tuple_dest_field(tuple_dests, *dest, *index, value_ty).is_ok();
                if !next_ok || !set_ok {
                    tuple_dests.remove(dest);
                }
            }
            t.nil()
        }
        Prim::DestFreeze { dest, token } => {
            if consume_init_token(init_tokens, *token).is_ok()
                && let Ok(fields) = freeze_tuple_dest(tuple_dests, *dest)
            {
                return t.tuple(&fields);
            }
            t.any()
        }
        Prim::DestListBegin { token } => {
            let _ = define_init_token(init_tokens, *token);
            let none = t.none();
            list_builders.insert(*token, t.list(none));
            t.nil()
        }
        Prim::DestListCons {
            token,
            head,
            tail,
            next,
        } => {
            let mut elem = lookup(t, env, *head);
            if let Some(tail) = tail {
                let tail_ty = lookup(t, env, *tail);
                let tail_elem = t.list_element_type(&tail_ty);
                elem = t.union(elem, tail_elem);
            }
            let cons_ty = t.non_empty_list(elem);
            if consume_init_token(init_tokens, *token).is_ok()
                && define_init_token(init_tokens, *next).is_ok()
            {
                list_builders.insert(*next, cons_ty.clone());
            }
            cons_ty
        }
        Prim::DestListFreeze { list, token } => {
            if consume_init_token(init_tokens, *token).is_ok()
                && let Some(ty) = list_builders.get(token).cloned()
            {
                return ty;
            }
            lookup(t, env, *list)
        }
        Prim::DestMapBegin { token, base, .. } => {
            let _ = define_init_token(init_tokens, *token);
            let map_ty = if let Some(base) = base {
                lookup(t, env, *base)
            } else {
                t.map(&[])
            };
            map_dests.insert(*token, map_ty.clone());
            map_ty
        }
        Prim::DestMapPut {
            map,
            token,
            key,
            value,
            next,
        } => {
            let current = map_dests
                .get(token)
                .cloned()
                .unwrap_or_else(|| lookup(t, env, *map));
            let value_ty = lookup(t, env, *value);
            let updated = if let Some(mk) = var_as_map_key(t, *key, env) {
                t.refine_map_field(&current, &mk, &value_ty)
            } else {
                t.map_top()
            };
            if consume_init_token(init_tokens, *token).is_ok()
                && define_init_token(init_tokens, *next).is_ok()
            {
                map_dests.insert(*next, updated);
            }
            t.nil()
        }
        Prim::DestMapFreeze { map, token } => {
            if consume_init_token(init_tokens, *token).is_ok()
                && let Some(ty) = map_dests.get(token).cloned()
            {
                return ty;
            }
            lookup(t, env, *map)
        }
        _ => type_prim(t, prim, env, m, const_vars),
    }
}

pub(crate) fn type_stmts_into_env<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    env: &mut HashMap<Var, crate::types::Ty>,
    stmts: &[Stmt],
    m: &Module,
) {
    let mut init_tokens: HashMap<InitTokenId, TokenState> = HashMap::new();
    let mut tuple_dests: HashMap<Var, TupleDestState<crate::types::Ty>> = HashMap::new();
    let mut list_builders: HashMap<InitTokenId, crate::types::Ty> = HashMap::new();
    let mut map_dests: HashMap<InitTokenId, crate::types::Ty> = HashMap::new();
    for stmt in stmts {
        let Stmt::Let(v, prim) = stmt;
        let pt_ty = type_let_with_init_facts(
            t,
            *v,
            prim,
            env,
            m,
            &HashSet::new(),
            &mut init_tokens,
            &mut tuple_dests,
            &mut list_builders,
            &mut map_dests,
        );
        env.insert(*v, pt_ty);
    }
}

pub fn type_fn<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    f: &FnIr,
    m: &Module,
    entry_param_types: Option<&[crate::types::Ty]>,
) -> FnTypes {
    // Pre-materialized fallbacks for the many `unwrap_or_else(any/none)`
    // sites. Re-cloned per fallback hit; future passes (when locals become Ty)
    // will let these flow as values instead of clone-on-fallback.
    let mut vars: HashMap<Var, crate::types::Ty> = HashMap::new();
    let mut block_envs: HashMap<BlockId, HashMap<Var, crate::types::Ty>> = HashMap::new();

    // Entry block: params come from the caller-narrowed `entry_param_types`
    // when provided (fz-ul4.27.10 module-level fixed point), or default to
    // `any` for the initial pass, fns with no direct caller (main,
    // closure-only targets), and fns that are closure-reachable (whose
    // caller set isn't bounded by the direct-call sites we can see).
    // Non-entry blocks: empty env, populated by goto/if predecessors.
    for b in &f.blocks {
        let mut env = HashMap::new();
        if b.id == f.entry {
            for (i, &p) in b.params.iter().enumerate() {
                let pt = entry_param_types
                    .and_then(|ts| ts.get(i))
                    .cloned()
                    .unwrap_or_else(|| t.any());
                env.insert(p, pt.clone());
                vars.insert(p, pt);
            }
        }
        block_envs.insert(b.id, env);
    }

    let topo = topo_order(f);
    loop {
        let mut changed = false;

        for &bid in &topo {
            let b = f.block(bid);
            // Re-derive env at each stmt position.
            let mut env = block_envs[&b.id].clone();
            // Track vars provably derived from IR-level Prim::Const stmts
            // within this block. Used to enable literal folding in
            // numeric_result_fold without cascading spec keys (fz-1pq.6).
            let mut const_vars: HashSet<Var> = HashSet::new();
            let mut init_tokens: HashMap<InitTokenId, TokenState> = HashMap::new();
            let mut tuple_dests: HashMap<Var, TupleDestState<crate::types::Ty>> = HashMap::new();
            let mut list_builders: HashMap<InitTokenId, crate::types::Ty> = HashMap::new();
            let mut map_dests: HashMap<InitTokenId, crate::types::Ty> = HashMap::new();
            for stmt in &b.stmts {
                let Stmt::Let(v, prim) = stmt;
                let pt_ty = type_let_with_init_facts(
                    t,
                    *v,
                    prim,
                    &env,
                    m,
                    &const_vars,
                    &mut init_tokens,
                    &mut tuple_dests,
                    &mut list_builders,
                    &mut map_dests,
                );
                // Propagate const-derivation: a Const is trivially const; a
                // BinOp/UnOp on const vars is also const.
                match prim {
                    Prim::Const(_) => {
                        const_vars.insert(*v);
                    }
                    Prim::BinOp(_, a, b) if const_vars.contains(a) && const_vars.contains(b) => {
                        const_vars.insert(*v);
                    }
                    Prim::UnOp(_, a) if const_vars.contains(a) => {
                        const_vars.insert(*v);
                    }
                    _ => {}
                }
                let pt = pt_ty.clone();
                env.insert(*v, pt.clone());
                // vars is the definition-site type; single assignment so
                // we just overwrite each iteration (will converge).
                let prev_ty = vars.get(v).cloned().unwrap_or_else(|| t.none());
                if !t.is_equivalent(&pt_ty, &prev_ty) {
                    vars.insert(*v, pt);
                    changed = true;
                }
            }

            // Propagate to successors.
            match &b.terminator {
                Term::Goto(target, args) => {
                    let target_b = f.block(*target);
                    let mut delta = env.clone();
                    // Substitute target's params with the supplied arg types.
                    let arg_ts: Vec<crate::types::Ty> = args
                        .iter()
                        .map(|a| env.get(a).cloned().unwrap_or_else(|| t.any()))
                        .collect();
                    // Remove anything keyed by the source-block's view of
                    // the args (they're not the same Vars as target params).
                    for (i, &p) in target_b.params.iter().enumerate() {
                        if let Some(at) = arg_ts.get(i) {
                            delta.insert(p, at.clone());
                        }
                    }
                    if merge_into(t, &mut block_envs, *target, &delta) {
                        changed = true;
                    }
                    // Update vars for target's params via union across all
                    // predecessors (handled via merge_into's union, but we
                    // also need to mirror in vars).
                    for &p in target_b.params.iter() {
                        let from_env = block_envs[target]
                            .get(&p)
                            .cloned()
                            .unwrap_or_else(|| t.none());
                        let prev_ty = vars.get(&p).cloned().unwrap_or_else(|| t.none());
                        if !t.is_equivalent(&from_env, &prev_ty) {
                            vars.insert(p, from_env);
                            changed = true;
                        }
                    }
                }
                Term::If {
                    cond,
                    then_b,
                    else_b,
                    ..
                } => {
                    let (then_env, else_env) = narrow_for_if(t, &env, *cond, &b.stmts);
                    if merge_into(t, &mut block_envs, *then_b, &then_env) {
                        changed = true;
                    }
                    if merge_into(t, &mut block_envs, *else_b, &else_env) {
                        changed = true;
                    }
                }
                Term::Call { .. }
                | Term::TailCall { .. }
                | Term::CallClosure { .. }
                | Term::TailCallClosure { .. }
                | Term::Return(_)
                | Term::Halt(_)
                | Term::Receive { .. }
                | Term::ReceiveMatched { .. } => {
                    // Inter-fn flow goes through separate FnIr continuations;
                    // intra-fn flow stops here.
                }
            }
        }

        if !changed {
            break;
        }
    }

    // fz-ul4.29.10.1 — populate fn_constants from zero-capture
    // `MakeClosure(F, [])` Let-bindings. Single forward pass; SSA
    // means each Var is bound at one site.
    let mut fn_constants: HashMap<Var, FnId> = HashMap::new();
    for b in &f.blocks {
        for stmt in &b.stmts {
            let Stmt::Let(v, prim) = stmt;
            if let Prim::MakeClosure(_, fid, captured) = prim
                && captured.is_empty()
            {
                fn_constants.insert(*v, *fid);
            }
        }
    }

    // fz-1pq.3 — post-convergence reachability pass. Worklist from
    // entry; at If terminators, use the post-stmt env (stmts may define
    // the condition var) to prune branches whose condition is a singleton
    // boolean (folded by compare_result).
    let mut reachable_blocks: HashSet<BlockId> = HashSet::new();
    let mut dead_branches: HashMap<BlockId, crate::fz_ir::DeadBranch> = HashMap::new();
    let mut worklist: Vec<BlockId> = vec![f.entry];
    while let Some(bid) = worklist.pop() {
        if !reachable_blocks.insert(bid) {
            continue;
        }
        let b = f.block(bid);
        match &b.terminator {
            Term::Goto(target, _) => worklist.push(*target),
            Term::If {
                cond,
                then_b,
                else_b,
                ..
            } => {
                // Re-evaluate stmts to get the env at the terminator.
                let mut env = block_envs[&bid].clone();
                type_stmts_into_env(t, &mut env, &b.stmts, m);
                let (then_env, else_env) = narrow_for_if(t, &env, *cond, &b.stmts);
                let mut then_dead = find_emptied_var(t, &env, &then_env).is_some();
                let mut else_dead = find_emptied_var(t, &env, &else_env).is_some();
                // Use both narrowing facts and singleton condition facts to
                // check provable branch deadness. `ct ⊆ true` means the else
                // branch is dead; `ct ⊆ false` means the then branch is dead.
                let ct_ty = env.get(cond).cloned().unwrap_or_else(|| t.none());
                let false_ty = t.atom_lit("false");
                let nil_ty = t.nil();
                if t.is_subtype(&ct_ty, &false_ty) || t.is_subtype(&ct_ty, &nil_ty) {
                    then_dead = true;
                }
                let true_ty = t.atom_lit("true");
                if t.is_subtype(&ct_ty, &true_ty) {
                    else_dead = true;
                }
                if then_dead && !else_dead {
                    dead_branches.insert(bid, crate::fz_ir::DeadBranch::Then);
                } else if else_dead && !then_dead {
                    dead_branches.insert(bid, crate::fz_ir::DeadBranch::Else);
                }
                if !then_dead {
                    worklist.push(*then_b);
                }
                if !else_dead {
                    worklist.push(*else_b);
                }
            }
            _ => {}
        }
    }

    FnTypes {
        vars,
        block_envs,
        fn_constants,
        reachable_blocks,
        dead_branches,
        dispatches: HashMap::new(),
        return_uses: HashMap::new(),
        list_tail_plans: HashMap::new(),
    }
}
