use super::expr_types::{lookup, var_as_map_key};
use super::fn_types::SpecPlan;
use super::narrow::{find_emptied_var, merge_into, narrow_for_if};
use super::prim::type_prim;
use crate::fz_ir::{BlockId, FnId, FnIr, InitTokenId, Module, Prim, Stmt, Term, Var};
use crate::ir_dest::{
    TokenState, TupleDestState, begin_tuple_dest, consume_init_token, define_init_token,
    freeze_tuple_dest, set_tuple_dest_field,
};
use std::collections::{HashMap, HashSet};

/// BFS from entry in discovery order. Already-visited successors are skipped;
/// the outer fixpoint in `type_fn` handles joins, cycles, and order imprecision.
/// Unreachable blocks are appended after the reachable prefix so their vars
/// still get typed.
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
) -> SpecPlan {
    let (mut vars, mut block_envs) = initialize_block_envs(t, f, entry_param_types);
    let topo = topo_order(f);
    run_type_fixed_point(t, f, m, &topo, &mut vars, &mut block_envs);
    let fn_constants = collect_fn_constants(f);
    let callable_capabilities = collect_callable_capabilities(t, f, &vars);
    let (reachable_blocks, dead_branches) =
        compute_reachable_blocks_and_dead_branches(t, f, m, &block_envs);
    SpecPlan {
        vars,
        block_envs,
        fn_constants,
        callable_capabilities,
        reachable_blocks,
        dead_branches,
        call_edges: HashMap::new(),
        extern_marshals: HashMap::new(),
    }
}

fn initialize_block_envs<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    f: &FnIr,
    entry_param_types: Option<&[crate::types::Ty]>,
) -> (
    HashMap<Var, crate::types::Ty>,
    HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
) {
    let mut vars = HashMap::new();
    let mut block_envs = HashMap::new();
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
    (vars, block_envs)
}

fn run_type_fixed_point<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    f: &FnIr,
    m: &Module,
    topo: &[BlockId],
    vars: &mut HashMap<Var, crate::types::Ty>,
    block_envs: &mut HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
) {
    loop {
        let mut changed = false;
        for &bid in topo {
            changed |= type_block_iteration(t, f, m, bid, vars, block_envs);
        }
        if !changed {
            break;
        }
    }
}

fn type_block_iteration<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    f: &FnIr,
    m: &Module,
    bid: BlockId,
    vars: &mut HashMap<Var, crate::types::Ty>,
    block_envs: &mut HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
) -> bool {
    let b = f.block(bid);
    let mut env = block_envs[&b.id].clone();
    let mut changed = type_stmts_for_fixed_point(t, m, &f.owner_module, &mut env, &b.stmts, vars);
    changed |= propagate_successors(t, f, b, &env, vars, block_envs);
    changed
}

fn type_stmts_for_fixed_point<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    m: &Module,
    owner: &str,
    env: &mut HashMap<Var, crate::types::Ty>,
    stmts: &[Stmt],
    vars: &mut HashMap<Var, crate::types::Ty>,
) -> bool {
    let mut changed = false;
    let mut const_vars: HashSet<Var> = HashSet::new();
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
            &const_vars,
            &mut init_tokens,
            &mut tuple_dests,
            &mut list_builders,
            &mut map_dests,
        );
        let pt_ty = t.mint_owned_resource_aliases(pt_ty, owner, &m.opaque_inners);
        record_const_derivation(*v, prim, &mut const_vars);
        env.insert(*v, pt_ty.clone());
        let prev_ty = vars.get(v).cloned().unwrap_or_else(|| t.none());
        if !t.is_equivalent(&pt_ty, &prev_ty) {
            vars.insert(*v, pt_ty);
            changed = true;
        }
    }
    changed
}

fn record_const_derivation(v: Var, prim: &Prim, const_vars: &mut HashSet<Var>) {
    match prim {
        Prim::Const(_) => {
            const_vars.insert(v);
        }
        Prim::BinOp(_, a, b) if const_vars.contains(a) && const_vars.contains(b) => {
            const_vars.insert(v);
        }
        Prim::UnOp(_, a) if const_vars.contains(a) => {
            const_vars.insert(v);
        }
        _ => {}
    }
}

fn propagate_successors<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    f: &FnIr,
    b: &crate::fz_ir::Block,
    env: &HashMap<Var, crate::types::Ty>,
    vars: &mut HashMap<Var, crate::types::Ty>,
    block_envs: &mut HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
) -> bool {
    match &b.terminator {
        Term::Goto(target, args) => propagate_goto(t, f, env, vars, block_envs, *target, args),
        Term::If {
            cond,
            then_b,
            else_b,
            ..
        } => propagate_if(t, b, env, block_envs, *cond, *then_b, *else_b),
        Term::Call { .. }
        | Term::TailCall { .. }
        | Term::CallClosure { .. }
        | Term::TailCallClosure { .. }
        | Term::Return(_)
        | Term::Halt(_)
        | Term::Receive { .. }
        | Term::ReceiveMatched { .. } => false,
    }
}

fn propagate_goto<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    f: &FnIr,
    env: &HashMap<Var, crate::types::Ty>,
    vars: &mut HashMap<Var, crate::types::Ty>,
    block_envs: &mut HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
    target: BlockId,
    args: &[Var],
) -> bool {
    let target_b = f.block(target);
    let mut delta = env.clone();
    let arg_ts: Vec<crate::types::Ty> = args
        .iter()
        .map(|a| env.get(a).cloned().unwrap_or_else(|| t.any()))
        .collect();
    for (i, &p) in target_b.params.iter().enumerate() {
        if let Some(at) = arg_ts.get(i) {
            delta.insert(p, at.clone());
        }
    }
    let mut changed = merge_into(t, block_envs, target, &delta);
    for &p in target_b.params.iter() {
        let from_env = block_envs[&target]
            .get(&p)
            .cloned()
            .unwrap_or_else(|| t.none());
        let prev_ty = vars.get(&p).cloned().unwrap_or_else(|| t.none());
        if !t.is_equivalent(&from_env, &prev_ty) {
            vars.insert(p, from_env);
            changed = true;
        }
    }
    changed
}

fn propagate_if<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    b: &crate::fz_ir::Block,
    env: &HashMap<Var, crate::types::Ty>,
    block_envs: &mut HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
    cond: Var,
    then_b: BlockId,
    else_b: BlockId,
) -> bool {
    let (then_env, else_env) = narrow_for_if(t, env, cond, &b.stmts);
    let then_changed = merge_into(t, block_envs, then_b, &then_env);
    let else_changed = merge_into(t, block_envs, else_b, &else_env);
    then_changed || else_changed
}

fn collect_fn_constants(f: &FnIr) -> HashMap<Var, FnId> {
    let mut fn_constants = HashMap::new();
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
    fn_constants
}

fn collect_callable_capabilities<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    f: &FnIr,
    vars: &HashMap<Var, crate::types::Ty>,
) -> HashMap<Var, super::fn_types::CallableCapability> {
    use super::fn_types::CallableCapability;

    let mut capabilities = HashMap::new();
    for b in &f.blocks {
        for stmt in &b.stmts {
            let Stmt::Let(v, prim) = stmt;
            if let Prim::MakeClosure(_, fid, captured) = prim {
                let cap = if captured.is_empty() {
                    CallableCapability::KnownFn(*fid)
                } else {
                    let captures = captured
                        .iter()
                        .filter_map(|cv| vars.get(cv).cloned())
                        .collect();
                    CallableCapability::KnownClosure {
                        fn_id: *fid,
                        captures,
                    }
                };
                capabilities.insert(*v, cap);
            }
        }
    }

    for (&v, ty) in vars {
        if capabilities.contains_key(&v) {
            continue;
        }
        let Some(clauses) = t.callable_clauses(ty) else {
            continue;
        };
        let mut closure_lits = clauses
            .into_iter()
            .filter_map(|clause| clause.closure)
            .collect::<Vec<_>>();
        closure_lits.sort_by_key(|lit| lit.target);
        closure_lits.dedup();
        let cap = match closure_lits.as_slice() {
            [lit] if lit.captures.is_empty() => CallableCapability::KnownFn(lit.target.into()),
            [lit] => CallableCapability::KnownClosure {
                fn_id: lit.target.into(),
                captures: lit.captures.clone(),
            },
            _ => CallableCapability::OpaqueCallable,
        };
        capabilities.insert(v, cap);
    }

    capabilities
}

fn compute_reachable_blocks_and_dead_branches<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    f: &FnIr,
    m: &Module,
    block_envs: &HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
) -> (HashSet<BlockId>, HashMap<BlockId, crate::fz_ir::DeadBranch>) {
    let mut reachable_blocks = HashSet::new();
    let mut dead_branches = HashMap::new();
    let mut worklist = vec![f.entry];
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
                let (then_dead, else_dead) = branch_deadness(t, m, block_envs, b, bid, *cond);
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
    (reachable_blocks, dead_branches)
}

fn branch_deadness<T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes>(
    t: &mut T,
    m: &Module,
    block_envs: &HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
    b: &crate::fz_ir::Block,
    bid: BlockId,
    cond: Var,
) -> (bool, bool) {
    let mut env = block_envs[&bid].clone();
    type_stmts_into_env(t, &mut env, &b.stmts, m);
    let (then_env, else_env) = narrow_for_if(t, &env, cond, &b.stmts);
    let mut then_dead = find_emptied_var(t, &env, &then_env).is_some();
    let mut else_dead = find_emptied_var(t, &env, &else_env).is_some();
    let ct_ty = env.get(&cond).cloned().unwrap_or_else(|| t.none());
    let false_ty = t.atom_lit("false");
    let nil_ty = t.nil();
    if t.is_subtype(&ct_ty, &false_ty) || t.is_subtype(&ct_ty, &nil_ty) {
        then_dead = true;
    }
    let true_ty = t.atom_lit("true");
    if t.is_subtype(&ct_ty, &true_ty) {
        else_dead = true;
    }
    (then_dead, else_dead)
}
