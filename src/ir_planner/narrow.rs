use crate::fz_ir::{BinOp, BlockId, Prim, Stmt, Var};
use crate::types::MapKey;
use std::collections::HashMap;

fn stmt_prim(stmts: &[Stmt], var: Var) -> Option<&Prim> {
    stmts.iter().find_map(|stmt| {
        let Stmt::Let(v, prim) = stmt;
        (*v == var).then_some(prim)
    })
}

fn bool_singleton_of_ty<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    ty: &crate::types::Ty,
) -> Option<bool> {
    let true_ty = t.bool_lit(true);
    if t.is_subtype(ty, &true_ty) {
        return Some(true);
    }
    let false_ty = t.bool_lit(false);
    if t.is_subtype(ty, &false_ty) {
        return Some(false);
    }
    None
}

fn known_bool_truth<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    stmts: &[Stmt],
    var: Var,
) -> Option<bool> {
    if let Some(ty) = env.get(&var)
        && let Some(value) = bool_singleton_of_ty(t, ty)
    {
        return Some(value);
    }
    match stmt_prim(stmts, var)? {
        Prim::IsEmptyList(v) => {
            let current_ty = env.get(v).cloned().unwrap_or_else(|| t.any());
            let empty_list = t.empty_list();
            if t.is_subtype(&current_ty, &empty_list) {
                Some(true)
            } else if t.is_disjoint(&current_ty, &empty_list) {
                Some(false)
            } else {
                None
            }
        }
        Prim::IsListCons(v) => {
            let current_ty = env.get(v).cloned().unwrap_or_else(|| t.any());
            let any = t.any();
            let cons_ty = t.non_empty_list(any);
            if t.is_subtype(&current_ty, &cons_ty) {
                Some(true)
            } else if t.is_disjoint(&current_ty, &cons_ty) {
                Some(false)
            } else {
                None
            }
        }
        Prim::IsMatcherMapMiss(v) => matcher_map_get_truth(t, env, stmts, *v),
        Prim::TypeTest(v, descr) => {
            let current_ty = env.get(v).cloned().unwrap_or_else(|| t.any());
            if t.is_subtype(&current_ty, descr) {
                Some(true)
            } else if t.is_disjoint(&current_ty, descr) {
                Some(false)
            } else {
                None
            }
        }
        Prim::BinOp(BinOp::Eq, a, b) => {
            let a_truth = known_bool_truth(t, env, stmts, *a);
            let b_truth = known_bool_truth(t, env, stmts, *b);
            match (a_truth, b_truth) {
                (Some(a_truth), Some(b_truth)) => Some(a_truth == b_truth),
                (Some(a_truth), None) => {
                    let b_ty = env.get(b).cloned().unwrap_or_else(|| t.any());
                    bool_singleton_of_ty(t, &b_ty).map(|b_truth| a_truth == b_truth)
                }
                (None, Some(b_truth)) => {
                    let a_ty = env.get(a).cloned().unwrap_or_else(|| t.any());
                    bool_singleton_of_ty(t, &a_ty).map(|a_truth| a_truth == b_truth)
                }
                (None, None) => None,
            }
        }
        Prim::BinOp(BinOp::Neq, a, b) => {
            let a_truth = known_bool_truth(t, env, stmts, *a);
            let b_truth = known_bool_truth(t, env, stmts, *b);
            match (a_truth, b_truth) {
                (Some(a_truth), Some(b_truth)) => Some(a_truth != b_truth),
                (Some(a_truth), None) => {
                    let b_ty = env.get(b).cloned().unwrap_or_else(|| t.any());
                    bool_singleton_of_ty(t, &b_ty).map(|b_truth| a_truth != b_truth)
                }
                (None, Some(b_truth)) => {
                    let a_ty = env.get(a).cloned().unwrap_or_else(|| t.any());
                    bool_singleton_of_ty(t, &a_ty).map(|a_truth| a_truth != b_truth)
                }
                (None, None) => None,
            }
        }
        _ => None,
    }
}

fn matcher_map_get_truth<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    stmts: &[Stmt],
    miss_var: Var,
) -> Option<bool> {
    let Prim::MatcherMapGet(map, key_var) = stmt_prim(stmts, miss_var)? else {
        return None;
    };
    let map_ty = env.get(map).cloned().unwrap_or_else(|| t.any());
    let key_ty = env.get(key_var).cloned().unwrap_or_else(|| t.any());
    let map_key: MapKey = t.as_map_key(&key_ty)?;

    let map_overlap = {
        let map_top = t.map_top();
        let overlap = t.intersect(map_ty.clone(), map_top);
        !t.is_empty(&overlap)
    };
    if !map_overlap {
        return Some(true);
    }

    let known_keys = t.map_known_keys(&map_ty);
    if known_keys.contains(&map_key) && t.map_field_lookup(&map_ty, &map_key).is_some() {
        return Some(false);
    }

    None
}

/// Union `delta` into `block_envs[target]`. Returns true if anything changed.
pub(crate) fn merge_into<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    block_envs: &mut HashMap<BlockId, HashMap<Var, crate::types::Ty>>,
    target: BlockId,
    delta: &HashMap<Var, crate::types::Ty>,
) -> bool {
    let env = block_envs.entry(target).or_default();
    let mut changed = false;
    for (v, dt) in delta {
        let prev_ty = env.get(v).cloned().unwrap_or_else(|| t.none());
        let unioned = t.union(prev_ty.clone(), dt.clone());
        if !t.is_equivalent(&unioned, &prev_ty) {
            env.insert(*v, unioned);
            changed = true;
        }
    }
    changed
}

/// Union two env maps, joining overlapping var types.
pub(crate) fn union_envs<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    a: HashMap<Var, crate::types::Ty>,
    b: &HashMap<Var, crate::types::Ty>,
) -> HashMap<Var, crate::types::Ty> {
    let mut out = a;
    for (v, dt) in b {
        let prev_ty = out.remove(v).unwrap_or_else(|| t.none());
        let unioned = t.union(prev_ty, dt.clone());
        out.insert(*v, unioned);
    }
    out
}

/// Recursive core for if-condition narrowing.
/// Returns (then_env, else_env) with variable types refined for each branch.
pub(crate) fn narrow_for_cond<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    cond: Var,
    env: &HashMap<Var, crate::types::Ty>,
    stmts: &[Stmt],
) -> (
    HashMap<Var, crate::types::Ty>,
    HashMap<Var, crate::types::Ty>,
) {
    let mut then_env = env.clone();
    let mut else_env = env.clone();

    let prim = stmts.iter().find_map(|s| {
        let Stmt::Let(v, p) = s;
        if *v == cond { Some(p) } else { None }
    });

    let Some(prim) = prim else {
        return (then_env, else_env);
    };

    if let Some(truth) = known_bool_truth(t, env, stmts, cond) {
        let true_ty = t.bool_lit(true);
        let false_ty = t.bool_lit(false);
        if truth {
            then_env.insert(cond, true_ty);
            else_env.insert(cond, t.none());
        } else {
            then_env.insert(cond, t.none());
            else_env.insert(cond, false_ty);
        }
        return (then_env, else_env);
    }

    // Helper: env-lookup → T::Ty with `any` fallback.
    let lookup_ty = |t: &mut T, env: &HashMap<Var, crate::types::Ty>, v: &Var| -> T::Ty {
        env.get(v).cloned().unwrap_or_else(|| t.any())
    };

    match prim {
        Prim::BinOp(BinOp::And, a, b) => {
            // Truthy: both sub-conditions hold — narrow by a, then by b.
            let (then_a, else_a) = narrow_for_cond(t, *a, env, stmts);
            let (then_ab, _) = narrow_for_cond(t, *b, &then_a, stmts);
            // Falsy: at least one fails — union of the individual false branches.
            let (_, else_b) = narrow_for_cond(t, *b, env, stmts);
            return (then_ab, union_envs(t, else_a, &else_b));
        }
        Prim::BinOp(BinOp::Or, a, b) => {
            // Truthy: at least one holds — union of individual true branches.
            let (then_a, else_a) = narrow_for_cond(t, *a, env, stmts);
            let (then_b, _) = narrow_for_cond(t, *b, env, stmts);
            // Falsy: both fail — narrow by a's false, then b's false.
            let (_, else_ab) = narrow_for_cond(t, *b, &else_a, stmts);
            return (union_envs(t, then_a, &then_b), else_ab);
        }
        Prim::IsEmptyList(v) => {
            // True narrows to the empty-list shape. False only subtracts that
            // one shape: non-list values are also definitely "not []" and must
            // remain possible.
            let current_ty = lookup_ty(t, env, v);
            let empty_list = t.empty_list();
            let then_t = t.intersect(current_ty.clone(), empty_list.clone());
            let else_t = t.difference(current_ty, empty_list);
            then_env.insert(*v, then_t);
            else_env.insert(*v, else_t);
        }
        Prim::IsListCons(v) => {
            let current_ty = lookup_ty(t, env, v);
            let any_inner = t.any();
            let cons_ty = t.non_empty_list(any_inner);
            let then_t = t.intersect(current_ty.clone(), cons_ty.clone());
            let else_t = t.difference(current_ty, cons_ty);
            then_env.insert(*v, then_t);
            else_env.insert(*v, else_t);
        }
        Prim::BinOp(BinOp::Eq, a, b) => {
            let at = lookup_ty(t, env, a);
            let bt = lookup_ty(t, env, b);
            // Truthy: intersect the non-singleton operand with the singleton.
            // Falsy: subtract the singleton from the non-singleton operand.
            if t.is_singleton_lit(&at) {
                let then_b = t.intersect(bt.clone(), at.clone());
                let else_b = t.difference(bt.clone(), at.clone());
                then_env.insert(*b, then_b);
                else_env.insert(*b, else_b);
            }
            if t.is_singleton_lit(&bt) {
                let then_a = t.intersect(at.clone(), bt.clone());
                let else_a = t.difference(at.clone(), bt.clone());
                then_env.insert(*a, then_a);
                else_env.insert(*a, else_a);
            }
        }
        Prim::BinOp(BinOp::Neq, a, b) => {
            // Mirror of Eq for `!=`: truthy subtracts the singleton, while
            // falsy intersects with it.
            let at = lookup_ty(t, env, a);
            let bt = lookup_ty(t, env, b);
            if t.is_singleton_lit(&at) {
                let else_b = t.intersect(bt.clone(), at.clone());
                let then_b = t.difference(bt.clone(), at.clone());
                else_env.insert(*b, else_b);
                then_env.insert(*b, then_b);
            }
            if t.is_singleton_lit(&bt) {
                let else_a = t.intersect(at.clone(), bt.clone());
                let then_a = t.difference(at.clone(), bt.clone());
                else_env.insert(*a, else_a);
                then_env.insert(*a, then_a);
            }
        }
        Prim::TypeTest(v, descr) => {
            let current_ty = lookup_ty(t, env, v);
            let then_t = t.intersect(current_ty.clone(), (**descr).clone());
            let else_t = t.difference(current_ty, (**descr).clone());
            then_env.insert(*v, then_t);
            else_env.insert(*v, else_t);
        }
        Prim::IsMatcherMapMiss(v) => match matcher_map_get_truth(t, env, stmts, *v) {
            Some(true) => {
                else_env.insert(*v, t.none());
            }
            Some(false) => {
                then_env.insert(*v, t.none());
            }
            None => {}
        },
        _ => {}
    }

    (then_env, else_env)
}

pub(crate) fn narrow_for_if<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    cond: Var,
    stmts: &[Stmt],
) -> (
    HashMap<Var, crate::types::Ty>,
    HashMap<Var, crate::types::Ty>,
) {
    narrow_for_cond(t, cond, env, stmts)
}

/// Within one spec's narrowed env, find the first Var whose type became empty
/// post-narrowing. Returns (Var, old_t, new_t) if found; None if narrowing kept
/// every var inhabited.
pub(crate) fn find_emptied_var<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    pre_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
    branch_env: &HashMap<crate::fz_ir::Var, crate::types::Ty>,
) -> Option<(crate::fz_ir::Var, T::Ty, T::Ty)> {
    let mut keys: Vec<crate::fz_ir::Var> = branch_env.keys().copied().collect();
    keys.sort_by_key(|v| v.0);
    for v in keys {
        let new_ty = branch_env.get(&v).unwrap().clone();
        let old_ty = pre_env.get(&v).cloned().unwrap_or_else(|| t.any());
        if !t.is_equivalent(&new_ty, &old_ty) && t.is_empty(&new_ty) && !t.is_empty(&old_ty) {
            return Some((v, old_ty, new_ty));
        }
    }
    None
}
