use crate::fz_ir::{BinOp, Const, Var};
use crate::types::MapKey;
use std::collections::HashMap;

pub(crate) fn type_const<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    c: &Const,
    atom_names: &[String],
) -> T::Ty {
    match c {
        Const::Int(n) => t.int_lit(*n),
        Const::Float(f) => t.float_lit(*f),
        Const::Atom(id) => {
            let name = atom_names
                .get(*id as usize)
                .map(String::as_str)
                .unwrap_or("?");
            t.atom_lit(name)
        }
        Const::Nil => t.nil(),
        Const::True => t.atom_lit("true"),
        Const::False => t.atom_lit("false"),
    }
}

pub(crate) fn type_binop<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    op: BinOp,
    a: &T::Ty,
    b: &T::Ty,
    fold: bool,
) -> T::Ty {
    use BinOp::*;
    match op {
        Add | Sub | Mul | Div | Mod => {
            if fold {
                numeric_result_fold(t, op, a, b)
            } else {
                numeric_result(t, a, b)
            }
        }
        Eq | Neq | Lt | Le | Gt | Ge => compare_result(t, op, a, b),
        And | Or => t.union(a.clone(), b.clone()),
    }
}

pub(crate) fn compare_result<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    op: BinOp,
    a: &T::Ty,
    b: &T::Ty,
) -> T::Ty {
    use BinOp::*;
    if let (Some(ai), Some(bi)) = (t.as_int_singleton(a), t.as_int_singleton(b)) {
        let result = match op {
            Eq => ai == bi,
            Neq => ai != bi,
            Lt => ai < bi,
            Le => ai <= bi,
            Gt => ai > bi,
            Ge => ai >= bi,
            _ => return t.bool(),
        };
        return if result {
            t.atom_lit("true")
        } else {
            t.atom_lit("false")
        };
    }
    if let (Some(af), Some(bf)) = (t.as_float_singleton(a), t.as_float_singleton(b)) {
        let result = match op {
            Eq => af == bf,
            Neq => af != bf,
            Lt => af < bf,
            Le => af <= bf,
            Gt => af > bf,
            Ge => af >= bf,
            _ => return t.bool(),
        };
        return if result {
            t.atom_lit("true")
        } else {
            t.atom_lit("false")
        };
    }
    t.bool()
}

pub(crate) fn numeric_result<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    a: &T::Ty,
    b: &T::Ty,
) -> T::Ty {
    let int_ty = t.int();
    let float_ty = t.float();
    let both_int = t.is_subtype(a, &int_ty) && t.is_subtype(b, &int_ty);
    let both_float = t.is_subtype(a, &float_ty) && t.is_subtype(b, &float_ty);
    if both_int {
        int_ty
    } else if both_float {
        float_ty
    } else {
        t.union(int_ty, float_ty)
    }
}

/// Like `numeric_result` but folds singleton operands to a literal result.
/// Called only when operands are literal-known, including synthetic literals
/// used to type unary negation.
pub(crate) fn numeric_result_fold<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    op: BinOp,
    a: &T::Ty,
    b: &T::Ty,
) -> T::Ty {
    use BinOp::*;
    if let (Some(ai), Some(bi)) = (t.as_int_singleton(a), t.as_int_singleton(b)) {
        let result = match op {
            Add => ai.checked_add(bi),
            Sub => ai.checked_sub(bi),
            Mul => ai.checked_mul(bi),
            Div => {
                if bi != 0 {
                    ai.checked_div(bi)
                } else {
                    None
                }
            }
            Mod => {
                if bi != 0 {
                    ai.checked_rem(bi)
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(r) = result {
            return t.int_lit(r);
        }
    }
    if let (Some(af), Some(bf)) = (t.as_float_singleton(a), t.as_float_singleton(b)) {
        let result = match op {
            Add => Some(af + bf),
            Sub => Some(af - bf),
            Mul => Some(af * bf),
            Div => Some(af / bf),
            Mod => Some(af % bf),
            _ => None,
        };
        if let Some(r) = result {
            return t.float_lit(r);
        }
    }
    numeric_result(t, a, b)
}

pub(crate) fn lookup<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    env: &HashMap<Var, crate::types::Ty>,
    v: Var,
) -> T::Ty {
    env.get(&v).cloned().unwrap_or_else(|| t.any())
}

pub(crate) fn var_as_map_key<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &T,
    v: Var,
    env: &HashMap<Var, crate::types::Ty>,
) -> Option<MapKey> {
    env.get(&v).and_then(|ty| t.as_map_key(ty))
}
