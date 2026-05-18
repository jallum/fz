//! fz-jg5.2 (RED.1) — Pattern reduction primitive.
//!
//! Pure functions used by the compile-time reducer (RED.3+).
//! `fold_prim` takes a `Prim` and an `env` of (Var → Descr) and returns
//! `Some(literal_descr)` when the Prim's output is uniquely determined,
//! `None` otherwise.
//!
//! Scope: scalars, tuples, closures, and TypeTest. List-structure folding
//! (e.g. ListHead/ListTail on a 5-element literal list) is NOT handled
//! here because list Descrs (`list_of(elem)`) lose length information —
//! that case wants IR-walking, which lands in RED.3.
//!
//! See `docs/walkthroughs/FINDINGS.md` for the refined rule set this
//! module embodies. In particular: kind-disjoint Eq/Neq folds even on
//! non-literal operands; `closure_lit(F, [literal captures])` is a
//! first-class literal Descr.

use crate::fz_ir::{BinOp, Const, Prim, UnOp, Var};
use crate::types::{Descr, F64Bits};
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// Literal-Descr predicates
// ---------------------------------------------------------------------------

/// True iff `d` uniquely determines a single runtime value.
///
/// Literal Descrs are the inputs `fold_prim` can act on and the outputs it
/// can produce. Recognized forms:
/// - Singleton int / float / atom / string.
/// - `nil` (and only nil).
/// - Single bool literal (`atom_lit("true")` or `atom_lit("false")`).
/// - Tuple whose every element is literal.
/// - Closure literal whose every capture is literal.
pub fn is_literal(d: &Descr) -> bool {
    as_int_lit(d).is_some()
        || as_float_lit(d).is_some()
        || as_atom_lit(d).is_some()
        || as_str_lit(d).is_some()
        || is_nil_only(d)
        || as_tuple_lit(d).is_some()
        || is_closure_lit_literal(d)
}

/// Singleton int. Mirrors `Descr::as_int_singleton`.
pub fn as_int_lit(d: &Descr) -> Option<i64> {
    d.as_int_singleton()
}

/// Singleton float.
pub fn as_float_lit(d: &Descr) -> Option<F64Bits> {
    if other_axes_empty_except("floats", d) && !d.floats.cofinite && d.floats.set.len() == 1 {
        d.floats.set.iter().next().copied()
    } else {
        None
    }
}

/// Singleton atom name.
pub fn as_atom_lit(d: &Descr) -> Option<&str> {
    if other_axes_empty_except("atoms", d) && !d.atoms.cofinite && d.atoms.set.len() == 1 {
        d.atoms.set.iter().next().map(String::as_str)
    } else {
        None
    }
}

/// Singleton string.
pub fn as_str_lit(d: &Descr) -> Option<&str> {
    if other_axes_empty_except("strs", d) && !d.strs.cofinite && d.strs.set.len() == 1 {
        d.strs.set.iter().next().map(String::as_str)
    } else {
        None
    }
}

/// `nil` and only nil.
pub fn is_nil_only(d: &Descr) -> bool {
    d.basic == crate::types::BasicBits::NIL
        && d.atoms.is_none()
        && d.ints.is_none()
        && d.floats.is_none()
        && d.strs.is_none()
        && d.tuples.is_empty()
        && d.lists.is_empty()
        && d.funcs.is_empty()
        && d.maps.is_empty()
        && d.opaques.is_none()
}

/// Single bool literal. Returns Some(true) for `atom_lit("true")` only,
/// Some(false) for `atom_lit("false")` only, None otherwise.
pub fn as_bool_lit(d: &Descr) -> Option<bool> {
    match as_atom_lit(d) {
        Some("true") => Some(true),
        Some("false") => Some(false),
        _ => None,
    }
}

/// Tuple of literal elements. Returns the element Descrs in order if every
/// element is literal; None otherwise.
pub fn as_tuple_lit(d: &Descr) -> Option<&[Descr]> {
    if !other_axes_empty_except("tuples", d) {
        return None;
    }
    if d.tuples.len() != 1 {
        return None;
    }
    let conj = &d.tuples[0];
    if !conj.neg.is_empty() || conj.pos.len() != 1 {
        return None;
    }
    let sig = &conj.pos[0];
    if sig.elems.iter().all(is_literal) {
        Some(&sig.elems)
    } else {
        None
    }
}

/// Closure literal with every capture literal.
fn is_closure_lit_literal(d: &Descr) -> bool {
    match d.as_closure_lit() {
        Some(lit) => lit.captures.iter().all(is_literal),
        None => false,
    }
}

/// Helper: every axis except the named one is empty.
fn other_axes_empty_except(axis: &str, d: &Descr) -> bool {
    let bits_ok = d.basic.is_empty();
    let atoms_ok = axis == "atoms" || d.atoms.is_none();
    let ints_ok = axis == "ints" || d.ints.is_none();
    let floats_ok = axis == "floats" || d.floats.is_none();
    let strs_ok = axis == "strs" || d.strs.is_none();
    let tuples_ok = axis == "tuples" || d.tuples.is_empty();
    let lists_ok = d.lists.is_empty();
    let funcs_ok = axis == "funcs" || d.funcs.is_empty();
    let maps_ok = d.maps.is_empty();
    let opaques_ok = d.opaques.is_none();
    bits_ok && atoms_ok && ints_ok && floats_ok && strs_ok && tuples_ok && lists_ok && funcs_ok
        && maps_ok && opaques_ok
}

// ---------------------------------------------------------------------------
// fold_prim
// ---------------------------------------------------------------------------

/// If the Prim's output is uniquely determined under `env`, return the
/// literal Descr. Otherwise None.
///
/// `atom_names` is the module's atom interner; `Const::Atom(id)` resolves
/// to `atom_lit(atom_names[id])`. Pass `&[]` if unused (Const::Atom will
/// return None).
pub fn fold_prim(
    prim: &Prim,
    env: &HashMap<Var, Descr>,
    atom_names: &[String],
) -> Option<Descr> {
    match prim {
        Prim::Const(c) => fold_const(c, atom_names),
        Prim::BinOp(op, a, b) => fold_binop(*op, *a, *b, env),
        Prim::UnOp(op, v) => fold_unop(*op, *v, env),
        Prim::MakeTuple(vs) => fold_make_tuple(vs, env),
        Prim::TupleField(v, i) => fold_tuple_field(*v, *i as usize, env),
        Prim::TypeTest(v, descr) => fold_type_test(*v, descr, env),
        // List structural folding requires IR-walking (RED.3+); the Descr
        // lattice's `list_of(elem)` loses length info. `ListIsNil` is the
        // exception — Descr-level subtyping is enough.
        Prim::ListIsNil(v) => fold_list_is_nil(*v, env),
        // Other Prims are not foldable via the Descr lattice in v1.
        Prim::Extern(..)
        | Prim::AllocStruct(..)
        | Prim::ListCons(..)
        | Prim::ListHead(..)
        | Prim::ListTail(..)
        | Prim::MakeList(..)
        | Prim::MakeClosure(..)
        | Prim::MakeMap(..)
        | Prim::MapUpdate(..)
        | Prim::MapGet(..)
        | Prim::MakeVec(..)
        | Prim::MakeBitstring(..)
        | Prim::ConstBitstring(..)
        | Prim::BitReaderInit(..)
        | Prim::BitReadField { .. }
        | Prim::BitReaderDone(..) => None,
    }
}

fn fold_const(c: &Const, atom_names: &[String]) -> Option<Descr> {
    let d = match c {
        Const::Int(n) => Descr::int_lit(*n),
        Const::Float(f) => Descr::float_lit(*f),
        Const::Str(s) => Descr::str_lit(s.clone()),
        Const::Nil => Descr::nil(),
        Const::True => Descr::atom_lit("true"),
        Const::False => Descr::atom_lit("false"),
        Const::Atom(id) => {
            let name = atom_names.get(*id as usize)?;
            Descr::atom_lit(name)
        }
    };
    Some(d)
}

fn fold_binop(op: BinOp, a: Var, b: Var, env: &HashMap<Var, Descr>) -> Option<Descr> {
    let ad = env.get(&a)?;
    let bd = env.get(&b)?;
    use BinOp::*;
    match op {
        Add | Sub | Mul | Div | Mod => fold_arith(op, ad, bd),
        Eq | Neq => fold_eq(op, ad, bd),
        Lt | Le | Gt | Ge => fold_cmp(op, ad, bd),
        And | Or => fold_logical(op, ad, bd),
    }
}

fn fold_arith(op: BinOp, ad: &Descr, bd: &Descr) -> Option<Descr> {
    if let (Some(ai), Some(bi)) = (as_int_lit(ad), as_int_lit(bd)) {
        let r = match op {
            BinOp::Add => ai.checked_add(bi)?,
            BinOp::Sub => ai.checked_sub(bi)?,
            BinOp::Mul => ai.checked_mul(bi)?,
            BinOp::Div => {
                if bi == 0 {
                    return None;
                }
                ai.checked_div(bi)?
            }
            BinOp::Mod => {
                if bi == 0 {
                    return None;
                }
                ai.checked_rem(bi)?
            }
            _ => return None,
        };
        return Some(Descr::int_lit(r));
    }
    if let (Some(af), Some(bf)) = (as_float_lit(ad), as_float_lit(bd)) {
        let af = af.get();
        let bf = bf.get();
        let r = match op {
            BinOp::Add => af + bf,
            BinOp::Sub => af - bf,
            BinOp::Mul => af * bf,
            BinOp::Div => af / bf,
            BinOp::Mod => af % bf,
            _ => return None,
        };
        if r.is_nan() {
            return None;
        }
        return Some(Descr::float_lit(r));
    }
    None
}

fn fold_eq(op: BinOp, ad: &Descr, bd: &Descr) -> Option<Descr> {
    let is_eq = matches!(op, BinOp::Eq);

    // Both literal: exact compare.
    if is_literal(ad) && is_literal(bd) {
        let equal = ad == bd;
        return Some(bool_descr(if is_eq { equal } else { !equal }));
    }

    // Kind-disjoint (intersection empty): result is definitively
    // false-for-Eq / true-for-Neq even without both being literal.
    if !ad.is_empty() && !bd.is_empty() && ad.intersect(bd).is_empty() {
        return Some(bool_descr(if is_eq { false } else { true }));
    }

    None
}

fn fold_cmp(op: BinOp, ad: &Descr, bd: &Descr) -> Option<Descr> {
    use BinOp::*;
    if let (Some(ai), Some(bi)) = (as_int_lit(ad), as_int_lit(bd)) {
        let b = match op {
            Lt => ai < bi,
            Le => ai <= bi,
            Gt => ai > bi,
            Ge => ai >= bi,
            _ => return None,
        };
        return Some(bool_descr(b));
    }
    if let (Some(af), Some(bf)) = (as_float_lit(ad), as_float_lit(bd)) {
        let af = af.get();
        let bf = bf.get();
        let b = match op {
            Lt => af < bf,
            Le => af <= bf,
            Gt => af > bf,
            Ge => af > bf || af == bf,
            _ => return None,
        };
        return Some(bool_descr(b));
    }
    None
}

fn fold_logical(op: BinOp, ad: &Descr, bd: &Descr) -> Option<Descr> {
    let ab = as_bool_lit(ad)?;
    let bb = as_bool_lit(bd)?;
    let r = match op {
        BinOp::And => ab && bb,
        BinOp::Or => ab || bb,
        _ => return None,
    };
    Some(bool_descr(r))
}

fn fold_unop(op: UnOp, v: Var, env: &HashMap<Var, Descr>) -> Option<Descr> {
    let d = env.get(&v)?;
    match op {
        UnOp::Neg => {
            if let Some(n) = as_int_lit(d) {
                return Some(Descr::int_lit(n.checked_neg()?));
            }
            if let Some(f) = as_float_lit(d) {
                return Some(Descr::float_lit(-f.get()));
            }
            None
        }
        UnOp::Not => as_bool_lit(d).map(|b| bool_descr(!b)),
    }
}

fn fold_make_tuple(vs: &[Var], env: &HashMap<Var, Descr>) -> Option<Descr> {
    let mut elems = Vec::with_capacity(vs.len());
    for v in vs {
        let d = env.get(v)?;
        if !is_literal(d) {
            return None;
        }
        elems.push(d.clone());
    }
    Some(Descr::tuple_of(elems))
}

fn fold_tuple_field(v: Var, i: usize, env: &HashMap<Var, Descr>) -> Option<Descr> {
    let d = env.get(&v)?;
    let elems = as_tuple_lit(d)?;
    elems.get(i).cloned()
}

fn fold_type_test(v: Var, descr: &Descr, env: &HashMap<Var, Descr>) -> Option<Descr> {
    let vd = env.get(&v)?;
    if vd.is_subtype(descr) {
        Some(bool_descr(true))
    } else if vd.intersect(descr).is_empty() {
        Some(bool_descr(false))
    } else {
        None
    }
}

fn fold_list_is_nil(v: Var, env: &HashMap<Var, Descr>) -> Option<Descr> {
    let d = env.get(&v)?;
    if is_nil_only(d) {
        Some(bool_descr(true))
    } else if d.intersect(&Descr::nil()).is_empty() && !d.lists.is_empty() {
        // Provably a cons (non-empty list) — not nil.
        Some(bool_descr(false))
    } else {
        None
    }
}

fn bool_descr(b: bool) -> Descr {
    Descr::atom_lit(if b { "true" } else { "false" })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::Var;

    fn v(n: u32) -> Var {
        Var(n)
    }

    fn env(pairs: &[(u32, Descr)]) -> HashMap<Var, Descr> {
        pairs.iter().map(|(i, d)| (Var(*i), d.clone())).collect()
    }

    // ---- is_literal predicates ----

    #[test]
    fn is_literal_recognizes_scalar_singletons() {
        assert!(is_literal(&Descr::int_lit(42)));
        assert!(is_literal(&Descr::float_lit(3.14)));
        assert!(is_literal(&Descr::atom_lit("foo")));
        assert!(is_literal(&Descr::str_lit("bar")));
        assert!(is_literal(&Descr::nil()));
        assert!(is_literal(&Descr::atom_lit("true")));
        assert!(is_literal(&Descr::atom_lit("false")));
    }

    #[test]
    fn is_literal_rejects_wide_types() {
        assert!(!is_literal(&Descr::int()));
        assert!(!is_literal(&Descr::float()));
        assert!(!is_literal(&Descr::any()));
        assert!(!is_literal(&Descr::bool_t())); // union of two atoms, not a singleton
    }

    #[test]
    fn is_literal_recognizes_literal_tuple() {
        let d = Descr::tuple_of([Descr::atom_lit("num"), Descr::int_lit(42)]);
        assert!(is_literal(&d));
    }

    #[test]
    fn is_literal_rejects_tuple_with_wide_element() {
        let d = Descr::tuple_of([Descr::atom_lit("num"), Descr::int()]);
        assert!(!is_literal(&d));
    }

    // ---- fold_const ----

    #[test]
    fn fold_const_int() {
        let r = fold_prim(&Prim::Const(Const::Int(42)), &HashMap::new(), &[]).unwrap();
        assert_eq!(as_int_lit(&r), Some(42));
    }

    #[test]
    fn fold_const_nil_and_bools() {
        let nil = fold_prim(&Prim::Const(Const::Nil), &HashMap::new(), &[]).unwrap();
        assert!(is_nil_only(&nil));
        let t = fold_prim(&Prim::Const(Const::True), &HashMap::new(), &[]).unwrap();
        assert_eq!(as_bool_lit(&t), Some(true));
        let f = fold_prim(&Prim::Const(Const::False), &HashMap::new(), &[]).unwrap();
        assert_eq!(as_bool_lit(&f), Some(false));
    }

    #[test]
    fn fold_const_atom_uses_atom_table() {
        let names = vec!["alpha".to_string(), "beta".to_string()];
        let a = fold_prim(&Prim::Const(Const::Atom(1)), &HashMap::new(), &names).unwrap();
        assert_eq!(as_atom_lit(&a), Some("beta"));
    }

    #[test]
    fn fold_const_atom_out_of_range_returns_none() {
        let names: Vec<String> = vec![];
        assert!(fold_prim(&Prim::Const(Const::Atom(0)), &HashMap::new(), &names).is_none());
    }

    // ---- arithmetic ----

    #[test]
    fn fold_int_add() {
        let env = env(&[(0, Descr::int_lit(41)), (1, Descr::int_lit(1))]);
        let r = fold_prim(&Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_int_lit(&r), Some(42));
    }

    #[test]
    fn fold_int_div_by_zero_returns_none() {
        let env = env(&[(0, Descr::int_lit(10)), (1, Descr::int_lit(0))]);
        assert!(fold_prim(&Prim::BinOp(BinOp::Div, v(0), v(1)), &env, &[]).is_none());
    }

    #[test]
    fn fold_int_overflow_returns_none() {
        let env = env(&[(0, Descr::int_lit(i64::MAX)), (1, Descr::int_lit(1))]);
        assert!(fold_prim(&Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).is_none());
    }

    #[test]
    fn fold_float_arith() {
        let env = env(&[(0, Descr::float_lit(1.5)), (1, Descr::float_lit(2.5))]);
        let r = fold_prim(&Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_float_lit(&r).map(|f| f.get()), Some(4.0));
    }

    #[test]
    fn fold_mixed_int_float_returns_none() {
        // No coercion; the typer's policy is no auto-promotion.
        let env = env(&[(0, Descr::int_lit(1)), (1, Descr::float_lit(2.0))]);
        assert!(fold_prim(&Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).is_none());
    }

    #[test]
    fn fold_arith_on_wide_input_returns_none() {
        let env = env(&[(0, Descr::int()), (1, Descr::int_lit(1))]);
        assert!(fold_prim(&Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).is_none());
    }

    // ---- comparison ----

    #[test]
    fn fold_int_lt() {
        let env = env(&[(0, Descr::int_lit(1)), (1, Descr::int_lit(2))]);
        let r = fold_prim(&Prim::BinOp(BinOp::Lt, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    // ---- equality + kind-disjoint fold ----

    #[test]
    fn fold_eq_literal_match() {
        let env = env(&[(0, Descr::int_lit(42)), (1, Descr::int_lit(42))]);
        let r = fold_prim(&Prim::BinOp(BinOp::Eq, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    #[test]
    fn fold_eq_literal_mismatch() {
        let env = env(&[(0, Descr::int_lit(42)), (1, Descr::int_lit(7))]);
        let r = fold_prim(&Prim::BinOp(BinOp::Eq, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(false));
    }

    #[test]
    fn fold_neq_literal_mismatch_is_true() {
        let env = env(&[(0, Descr::int_lit(42)), (1, Descr::int_lit(7))]);
        let r = fold_prim(&Prim::BinOp(BinOp::Neq, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    #[test]
    fn fold_eq_kind_disjoint_non_literal() {
        // int vs atom_top: kinds disjoint at the lattice level.
        // VR.5a's case — fold to false even though operands aren't literal.
        let env = env(&[(0, Descr::int()), (1, Descr::atom_top())]);
        let r = fold_prim(&Prim::BinOp(BinOp::Eq, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(false));
        let r = fold_prim(&Prim::BinOp(BinOp::Neq, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    #[test]
    fn fold_eq_overlapping_non_literal_returns_none() {
        // int vs int: kinds overlap; cannot decide statically.
        let env = env(&[(0, Descr::int()), (1, Descr::int())]);
        assert!(fold_prim(&Prim::BinOp(BinOp::Eq, v(0), v(1)), &env, &[]).is_none());
    }

    // ---- logical ----

    #[test]
    fn fold_and_bool_lits() {
        let env = env(&[
            (0, Descr::atom_lit("true")),
            (1, Descr::atom_lit("false")),
        ]);
        let r = fold_prim(&Prim::BinOp(BinOp::And, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(false));
        let env = env_with_true();
        let r = fold_prim(&Prim::BinOp(BinOp::Or, v(0), v(1)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    fn env_with_true() -> HashMap<Var, Descr> {
        env(&[
            (0, Descr::atom_lit("true")),
            (1, Descr::atom_lit("false")),
        ])
    }

    // ---- unary ----

    #[test]
    fn fold_neg_int() {
        let env = env(&[(0, Descr::int_lit(5))]);
        let r = fold_prim(&Prim::UnOp(UnOp::Neg, v(0)), &env, &[]).unwrap();
        assert_eq!(as_int_lit(&r), Some(-5));
    }

    #[test]
    fn fold_not_bool() {
        let env = env(&[(0, Descr::atom_lit("true"))]);
        let r = fold_prim(&Prim::UnOp(UnOp::Not, v(0)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(false));
    }

    // ---- tuple ----

    #[test]
    fn fold_make_tuple_of_literals() {
        let env = env(&[(0, Descr::atom_lit("num")), (1, Descr::int_lit(42))]);
        let r = fold_prim(&Prim::MakeTuple(vec![v(0), v(1)]), &env, &[]).unwrap();
        let elems = as_tuple_lit(&r).unwrap();
        assert_eq!(elems.len(), 2);
        assert_eq!(as_atom_lit(&elems[0]), Some("num"));
        assert_eq!(as_int_lit(&elems[1]), Some(42));
    }

    #[test]
    fn fold_make_tuple_with_wide_element_is_none() {
        let env = env(&[(0, Descr::atom_lit("num")), (1, Descr::int())]);
        assert!(fold_prim(&Prim::MakeTuple(vec![v(0), v(1)]), &env, &[]).is_none());
    }

    #[test]
    fn fold_tuple_field_literal() {
        let t = Descr::tuple_of([Descr::atom_lit("num"), Descr::int_lit(42)]);
        let env = env(&[(0, t)]);
        let r = fold_prim(&Prim::TupleField(v(0), 1), &env, &[]).unwrap();
        assert_eq!(as_int_lit(&r), Some(42));
        let r = fold_prim(&Prim::TupleField(v(0), 0), &env, &[]).unwrap();
        assert_eq!(as_atom_lit(&r), Some("num"));
    }

    #[test]
    fn fold_tuple_field_out_of_range() {
        let t = Descr::tuple_of([Descr::atom_lit("num"), Descr::int_lit(42)]);
        let env = env(&[(0, t)]);
        assert!(fold_prim(&Prim::TupleField(v(0), 7), &env, &[]).is_none());
    }

    // ---- type test ----

    #[test]
    fn fold_type_test_proves_true() {
        let env = env(&[(0, Descr::int_lit(42))]);
        let r = fold_prim(
            &Prim::TypeTest(v(0), Box::new(Descr::int())),
            &env,
            &[],
        )
        .unwrap();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    #[test]
    fn fold_type_test_proves_false() {
        let env = env(&[(0, Descr::int_lit(42))]);
        let r = fold_prim(
            &Prim::TypeTest(v(0), Box::new(Descr::atom_top())),
            &env,
            &[],
        )
        .unwrap();
        assert_eq!(as_bool_lit(&r), Some(false));
    }

    #[test]
    fn fold_type_test_undecidable_returns_none() {
        let env = env(&[(0, Descr::any())]);
        assert!(fold_prim(
            &Prim::TypeTest(v(0), Box::new(Descr::int())),
            &env,
            &[]
        )
        .is_none());
    }

    // ---- list_is_nil ----

    #[test]
    fn fold_list_is_nil_on_nil() {
        let env = env(&[(0, Descr::nil())]);
        let r = fold_prim(&Prim::ListIsNil(v(0)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    #[test]
    fn fold_list_is_nil_on_list_of_int() {
        let env = env(&[(0, Descr::list_of(Descr::int_lit(1)))]);
        let r = fold_prim(&Prim::ListIsNil(v(0)), &env, &[]).unwrap();
        assert_eq!(as_bool_lit(&r), Some(false));
    }

    #[test]
    fn fold_list_is_nil_on_maybe_empty_returns_none() {
        // list_of(int) | nil — could be either.
        let env = env(&[(0, Descr::list_of(Descr::int_lit(1)).union(&Descr::nil()))]);
        assert!(fold_prim(&Prim::ListIsNil(v(0)), &env, &[]).is_none());
    }

    // ---- non-foldable prims explicitly return None ----

    #[test]
    fn fold_extern_returns_none() {
        use crate::fz_ir::ExternId;
        let env = HashMap::new();
        assert!(
            fold_prim(
                &Prim::Extern(ExternId(0), vec![]),
                &env,
                &[],
            )
            .is_none()
        );
    }

    #[test]
    fn fold_make_list_returns_none() {
        // Lists are folded by IR-walking in RED.3+, not by fold_prim.
        let env = env(&[(0, Descr::int_lit(1)), (1, Descr::int_lit(2))]);
        assert!(fold_prim(&Prim::MakeList(vec![v(0), v(1)], None), &env, &[]).is_none());
    }

    // Bitstring construction / reader prims aren't foldable in v1; covered
    // by the explicit None-returning match arms in `fold_prim`. ConstBitstring
    // and friends are exercised by the wider codegen tests, not here.
}
