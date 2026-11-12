//! Type-predicate helpers used by codegen lowering decisions.

use std::collections::HashMap;

use crate::compiler2::Ty;
use crate::fz_ir::Var;
use crate::types::Types;

pub(crate) fn var_ty_satisfies<T: Types<Ty = Ty>>(
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    v: Var,
    want: T::Ty,
) -> bool {
    let got = value_types.get(&v).cloned().unwrap_or_else(|| t.any());
    t.is_subtype(&got, &want)
}

/// True when `v`'s typer-inferred type is a subtype of `int_top` — the
/// arithmetic dispatch elision pre-condition.
pub(crate) fn ty_is_int<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let want = t.int();
    var_ty_satisfies(t, value_types, v, want)
}

/// True when `v`'s typer-inferred type is a subtype of `float` — the
/// float-arithmetic dispatch elision pre-condition.
pub(crate) fn ty_is_float<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let want = t.float();
    var_ty_satisfies(t, value_types, v, want)
}

/// True when `v`'s typer-inferred type is a subtype of `atom_top`.
/// Atom-monomorphic Eq/Neq lowers to a single icmp because two AnyValues
/// with the same atom-id share the same bit pattern.
pub(crate) fn ty_is_atom<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let want = t.atom();
    var_ty_satisfies(t, value_types, v, want)
}

pub(crate) fn ty_is_list<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let elem = t.any();
    let want = t.list(elem);
    var_ty_satisfies(t, value_types, v, want)
}

pub(crate) fn ty_is_empty_list<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let want = t.empty_list();
    var_ty_satisfies(t, value_types, v, want)
}

pub(crate) fn ty_is_non_empty_list<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let elem = t.any();
    let want = t.non_empty_list(elem);
    var_ty_satisfies(t, value_types, v, want)
}

pub(crate) fn list_projection_is_safe<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    ty_is_non_empty_list(t, value_types, v)
}

pub(crate) fn ty_is_map<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let want = t.map_top();
    var_ty_satisfies(t, value_types, v, want)
}

pub(crate) fn ty_is_tuple<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let got = value_types.get(&v).cloned().unwrap_or_else(|| t.any());
    t.is_tuple_type(&got)
}

/// True when every value of `v`'s type is a tuple, a map or a binary: an
/// object a reference names by its address. Such a reference is never a list,
/// whose spine a holder must share, and never a boxed scalar, whose value
/// sits behind the reference.
pub(crate) fn ty_is_addressed_object<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let tuples = t.tuple_top();
    let maps = t.map_top();
    let binaries = t.str_t();
    let objects = t.union(tuples, maps);
    let objects = t.union(objects, binaries);
    value_types.get(&v).is_some_and(|got| t.is_subtype(got, &objects))
}

/// True when `v` is statically nil-or-bool. Both occupy disjoint, fixed raw
/// atom payloads, so equality on them is bit-eq when the kind is known.
pub(crate) fn descr_is_nil_or_bool<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let nil = t.nil();
    let bool_t = t.bool();
    let nb = t.union(nil, bool_t);
    var_ty_satisfies(t, value_types, v, nb)
}

/// fz-bsx.3 — true when no two runtime values of the operands' types can
/// ever be equal: disjointness in the brand-erased (runtime) model. This is
/// the ONLY disjointness that may authorize folding `==`/`!=` to a constant.
/// The type value carries the nominal structure needed to erase brand/opaque
/// tags because `==` is brand-blind at runtime (lowering erases brands +
/// byte-wise `fz_value_eq`).
/// Using the brand-AWARE `is_disjoint` here was the fz-bsx bug.
pub(crate) fn descrs_value_disjoint<T: Types<Ty = Ty>>(t: &T, value_types: &HashMap<Var, Ty>, a: Var, b: Var) -> bool {
    match (value_types.get(&a), value_types.get(&b)) {
        (Some(da), Some(db)) => t.is_value_disjoint(da, db),
        _ => false,
    }
}
