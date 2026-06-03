//! Type-predicate helpers used by codegen lowering decisions.

use std::collections::HashMap;

use crate::fz_ir::Var;
use crate::ir_planner::SpecPlan;
use crate::types::{Ty, Types};

pub(crate) fn var_ty_satisfies<T: Types<Ty = Ty>>(t: &mut T, fn_types: &SpecPlan, v: Var, want: T::Ty) -> bool {
    let got = fn_types.vars.get(&v).cloned().unwrap_or_else(|| t.any());
    t.is_subtype(&got, &want)
}

/// True when `v`'s typer-inferred type is a subtype of `int_top` — the
/// arithmetic dispatch elision pre-condition.
pub(crate) fn ty_is_int<T: Types<Ty = Ty>>(t: &mut T, fn_types: &SpecPlan, v: Var) -> bool {
    let want = t.int();
    var_ty_satisfies(t, fn_types, v, want)
}

/// True when `v`'s typer-inferred type is a subtype of `float` — the
/// float-arithmetic dispatch elision pre-condition.
pub(crate) fn ty_is_float<T: Types<Ty = Ty>>(t: &mut T, fn_types: &SpecPlan, v: Var) -> bool {
    let want = t.float();
    var_ty_satisfies(t, fn_types, v, want)
}

/// True when `v`'s typer-inferred type is a subtype of `atom_top`.
/// Atom-monomorphic Eq/Neq lowers to a single icmp because two AnyValues
/// with the same atom-id share the same bit pattern.
pub(crate) fn ty_is_atom<T: Types<Ty = Ty>>(t: &mut T, fn_types: &SpecPlan, v: Var) -> bool {
    let want = t.atom();
    var_ty_satisfies(t, fn_types, v, want)
}

pub(crate) fn ty_is_list<T: Types<Ty = Ty>>(t: &mut T, fn_types: &SpecPlan, v: Var) -> bool {
    let elem = t.any();
    let want = t.list(elem);
    var_ty_satisfies(t, fn_types, v, want)
}

pub(crate) fn var_ty_satisfies_in_context<T: Types<Ty = Ty>>(
    t: &mut T,
    fn_types: &SpecPlan,
    v: Var,
    want: Ty,
    block_env: Option<&HashMap<Var, Ty>>,
) -> bool {
    var_ty_satisfies(t, fn_types, v, want.clone())
        || block_env.is_some_and(|env| {
            let Some(got) = env.get(&v).cloned() else {
                return false;
            };
            t.is_subtype(&got, &want)
        })
}

pub(crate) fn ty_is_empty_list_in_context<T: Types<Ty = Ty>>(
    t: &mut T,
    fn_types: &SpecPlan,
    v: Var,
    block_env: Option<&HashMap<Var, Ty>>,
) -> bool {
    let want = t.empty_list();
    var_ty_satisfies_in_context(t, fn_types, v, want, block_env)
}

pub(crate) fn ty_is_non_empty_list_in_context<T: Types<Ty = Ty>>(
    t: &mut T,
    fn_types: &SpecPlan,
    v: Var,
    block_env: Option<&HashMap<Var, Ty>>,
) -> bool {
    let elem = t.any();
    let want = t.non_empty_list(elem);
    var_ty_satisfies_in_context(t, fn_types, v, want, block_env)
}

pub(crate) fn list_projection_is_safe<T: Types<Ty = Ty>>(
    t: &mut T,
    fn_types: &SpecPlan,
    v: Var,
    block_env: Option<&HashMap<Var, Ty>>,
) -> bool {
    ty_is_non_empty_list_in_context(t, fn_types, v, block_env)
}

pub(crate) fn ty_is_map<T: Types<Ty = Ty>>(t: &mut T, fn_types: &SpecPlan, v: Var) -> bool {
    let want = t.map_top();
    var_ty_satisfies(t, fn_types, v, want)
}

pub(crate) fn ty_has_tuple<T: Types<Ty = Ty>>(t: &mut T, fn_types: &SpecPlan, v: Var) -> bool {
    let got = fn_types.vars.get(&v).cloned().unwrap_or_else(|| t.any());
    t.max_tuple_arity(&got) > 0
}

/// True when `v` is statically nil-or-bool. Both occupy disjoint, fixed raw
/// atom payloads, so equality on them is bit-eq when the kind is known.
pub(crate) fn descr_is_nil_or_bool<T: Types<Ty = Ty>>(t: &mut T, fn_types: &SpecPlan, v: Var) -> bool {
    let nil = t.nil();
    let bool_t = t.bool();
    let nb = t.union(nil, bool_t);
    var_ty_satisfies(t, fn_types, v, nb)
}

/// fz-bsx.3 — true when no two runtime values of the operands' types can
/// ever be equal: disjointness in the brand-erased (runtime) model. This is
/// the ONLY disjointness that may authorize folding `==`/`!=` to a constant.
/// Brand/opaque tags are discharged via the spec's inner-type maps, because
/// `==` is brand-blind at runtime (`ir_brand_erase` + byte-wise `fz_value_eq`).
/// Using the brand-AWARE `is_disjoint` here was the fz-bsx bug.
pub(crate) fn descrs_value_disjoint<T: Types<Ty = Ty>>(t: &T, fn_types: &SpecPlan, a: Var, b: Var) -> bool {
    match (fn_types.vars.get(&a), fn_types.vars.get(&b)) {
        (Some(da), Some(db)) => t.is_value_disjoint(da, db, fn_types.nominals()),
        _ => false,
    }
}
