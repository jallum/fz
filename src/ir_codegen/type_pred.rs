//! Type-predicate helpers used by codegen lowering decisions.

use std::collections::HashMap;

pub(crate) fn var_ty_satisfies<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
    want: T::Ty,
) -> bool {
    let got = fn_types.vars.get(&v).cloned().unwrap_or_else(|| t.any());
    t.is_subtype(&got, &want)
}

/// True when `v`'s typer-inferred type is a subtype of `int_top` — the
/// arithmetic dispatch elision pre-condition (.11.24.4).
pub(crate) fn ty_is_int<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
) -> bool {
    let want = t.int();
    var_ty_satisfies(t, fn_types, v, want)
}

/// True when `v`'s typer-inferred type is a subtype of `float` — the
/// float-arithmetic dispatch elision pre-condition (fz-ul4.27.3).
pub(crate) fn ty_is_float<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
) -> bool {
    let want = t.float();
    var_ty_satisfies(t, fn_types, v, want)
}

/// True when `v`'s typer-inferred type is a subtype of `atom_top`.
/// VR.5a: atom-monomorphic Eq/Neq lowers to a single icmp because two
/// AnyValues with the same atom-id share the same bit pattern.
pub(crate) fn ty_is_atom<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
) -> bool {
    let want = t.atom();
    var_ty_satisfies(t, fn_types, v, want)
}

pub(crate) fn ty_is_list<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
) -> bool {
    let elem = t.any();
    let want = t.list(elem);
    var_ty_satisfies(t, fn_types, v, want)
}

pub(crate) fn var_ty_satisfies_in_context<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
    want: crate::types::Ty,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
) -> bool {
    var_ty_satisfies(t, fn_types, v, want.clone())
        || block_env.is_some_and(|env| {
            let Some(got) = env.get(&v).cloned() else {
                return false;
            };
            t.is_subtype(&got, &want)
        })
}

pub(crate) fn ty_is_empty_list_in_context<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
) -> bool {
    let want = t.empty_list();
    var_ty_satisfies_in_context(t, fn_types, v, want, block_env)
}

pub(crate) fn ty_is_non_empty_list_in_context<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
) -> bool {
    let elem = t.any();
    let want = t.non_empty_list(elem);
    var_ty_satisfies_in_context(t, fn_types, v, want, block_env)
}

pub(crate) fn list_projection_is_safe<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
) -> bool {
    ty_is_non_empty_list_in_context(t, fn_types, v, block_env)
}

pub(crate) fn ty_is_map<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
) -> bool {
    let want = t.map_top();
    var_ty_satisfies(t, fn_types, v, want)
}

pub(crate) fn ty_has_tuple<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
) -> bool {
    let got = fn_types.vars.get(&v).cloned().unwrap_or_else(|| t.any());
    t.max_tuple_arity(&got) > 0
}

/// True when `v` is statically nil-or-bool. Both occupy disjoint, fixed raw
/// atom payloads, so equality on them is bit-eq when the kind is known.
pub(crate) fn descr_is_nil_or_bool<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    v: crate::fz_ir::Var,
) -> bool {
    let nil = t.nil();
    let bool_t = t.bool();
    let nb = t.union(nil, bool_t);
    var_ty_satisfies(t, fn_types, v, nb)
}

/// True when the two operands' types have empty intersection — Eq folds to
/// false, Neq folds to true. VR.5a powers both the lowering shortcut and
/// the `type/dead-binop` diagnostic.
pub(crate) fn descrs_disjoint<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &T,
    fn_types: &crate::ir_planner::SpecPlan,
    a: crate::fz_ir::Var,
    b: crate::fz_ir::Var,
) -> bool {
    match (fn_types.vars.get(&a), fn_types.vars.get(&b)) {
        (Some(da), Some(db)) => t.is_disjoint(da, db),
        _ => false,
    }
}
