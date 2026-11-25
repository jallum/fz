//! Type-predicate helpers used by codegen lowering decisions.

use crate::fast_hash::HashMap;

use super::list_cell::ListShape;
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

/// True when `v`'s typer-inferred type is a subtype of `bitstring`: every value
/// of it is a binary of either layout, or a bitstring that is not whole bytes.
pub(crate) fn ty_is_bitstring<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let want = t.bitstring();
    var_ty_satisfies(t, value_types, v, want)
}

pub(crate) fn ty_is_list<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let elem = t.any();
    let want = t.list(elem);
    var_ty_satisfies(t, value_types, v, want)
}

/// True when every value of `v`'s type is a list, proper or not.
pub(crate) fn ty_is_any_list<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let want = t.any_list();
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

/// Where the list `v` names ends, as its type proves it: a list type with no
/// improper member ends in `[]`.
pub(crate) fn list_shape<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> ListShape {
    if ty_is_non_empty_list(t, value_types, v) {
        ListShape::Proper
    } else {
        ListShape::MayEndInAValue
    }
}

pub(crate) fn ty_is_map<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let want = t.map_top();
    var_ty_satisfies(t, value_types, v, want)
}

pub(crate) fn ty_is_tuple<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> bool {
    let got = value_types.get(&v).cloned().unwrap_or_else(|| t.any());
    t.is_tuple_type(&got)
}

/// How a store shares `v`, when every value of `v`'s type is a tuple, a map
/// or a bitstring: an object a reference names by its address. Such a
/// reference is never a list, whose spine a holder must share, and never a
/// boxed scalar, whose value sits behind the reference. `None` when the type
/// allows either.
pub(crate) fn addressed_object_share<T: Types<Ty = Ty>>(
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    v: Var,
) -> Option<ShareClass> {
    let tuples = t.tuple_top();
    let maps = t.map_top();
    let bitstrings = t.bitstring();
    let objects = t.union(tuples, maps);
    let objects = t.union(objects, bitstrings);
    let addressed = value_types.get(&v).is_some_and(|got| t.is_subtype(got, &objects));
    addressed.then(|| share_class(t, value_types, v))
}

/// What sharing `v` must do, by its type.
pub(crate) enum ShareClass {
    /// Every value of the type is a number or an atom, which carries no mark.
    Markless,
    /// Every value of the type keeps its mark the way objects of this kind
    /// do: a binary of either layout, a tuple, or a list.
    Kind(fz_runtime::any_value::ValueKind),
    /// The type does not say; the reference's kind does, when the program runs.
    Dynamic,
}

pub(crate) fn share_class<T: Types<Ty = Ty>>(t: &mut T, value_types: &HashMap<Var, Ty>, v: Var) -> ShareClass {
    use fz_runtime::any_value::ValueKind;
    let int = t.int();
    let float = t.float();
    let atom = t.atom();
    let numbers = t.union(int, float);
    let markless = t.union(numbers, atom);
    if var_ty_satisfies(t, value_types, v, markless) {
        return ShareClass::Markless;
    }
    let bitstrings = t.bitstring();
    if var_ty_satisfies(t, value_types, v, bitstrings) {
        return ShareClass::Kind(ValueKind::BITSTRING);
    }
    let tuples = t.tuple_top();
    if var_ty_satisfies(t, value_types, v, tuples) {
        return ShareClass::Kind(ValueKind::STRUCT);
    }
    if ty_is_list(t, value_types, v) {
        return ShareClass::Kind(ValueKind::LIST);
    }
    ShareClass::Dynamic
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
