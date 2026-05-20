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

use crate::ast::{self, Pattern, Spanned};
use crate::fz_ir::{BinOp, Const, Prim, UnOp, Var};
use crate::types::{Descr, F64Bits};
use crate::types_seam::{AsDescr, Types};
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
    d.as_float_singleton()
}

/// Singleton atom name.
pub fn as_atom_lit(d: &Descr) -> Option<&str> {
    d.as_atom_singleton()
}

/// `nil` and only nil.
pub fn is_nil_only(d: &Descr) -> bool {
    // fz-yan.2 — `nil` is the `:nil` atom literal; check the atoms axis,
    // not BasicBits.
    as_atom_lit(d) == Some("nil")
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
    let elems = d.as_tuple_singleton()?;
    if elems.iter().all(is_literal) {
        Some(elems)
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

// ---------------------------------------------------------------------------
// fold_prim
// ---------------------------------------------------------------------------

/// If the Prim's output is uniquely determined under `env`, return the
/// literal Descr. Otherwise None.
///
/// `atom_names` is the module's atom interner; `Const::Atom(id)` resolves
/// to `atom_lit(atom_names[id])`. Pass `&[]` if unused (Const::Atom will
/// return None).
pub fn fold_prim<T: Types>(
    t: &mut T,
    prim: &Prim,
    env: &HashMap<Var, Descr>,
    atom_names: &[String],
) -> Option<T::Ty> {
    match prim {
        Prim::Const(c) => fold_const(t, c, atom_names),
        Prim::BinOp(op, a, b) => fold_binop(t, *op, *a, *b, env),
        Prim::UnOp(op, v) => fold_unop(t, *op, *v, env),
        Prim::MakeTuple(vs) => fold_make_tuple(t, vs, env),
        Prim::TupleField(v, i) => fold_tuple_field(t, *v, *i as usize, env),
        Prim::TypeTest(v, descr) => fold_type_test(t, *v, descr, env),
        // List structural folding requires IR-walking (RED.3+); the Descr
        // lattice's `list_of(elem)` loses length info. `IsEmptyList` is the
        // exception — Descr-level subtyping is enough.
        Prim::IsEmptyList(v) => fold_list_is_nil(t, *v, env),
        // fz-f88.3 — empty list literal folds to `list_of(none())`. Non-empty
        // MakeList still loses length info (L1 follow-up fz-4lo).
        Prim::MakeList(elems, tail_v) if elems.is_empty() && tail_v.is_none() => {
            Some(t.from_descr(&Descr::list_of(Descr::none())))
        }
        // fz-jg5.6: closure_lit fold — when MakeClosure's captures are
        // all literal, the closure Var has a closure_lit(F, captures) Descr.
        // The reducer's walk_block uses this to dispatch CallClosure /
        // TailCallClosure to F directly.
        Prim::MakeClosure(_, fn_id, captured) => fold_make_closure(t, *fn_id, captured, env),
        // Other Prims are not foldable via the Descr lattice in v1.
        Prim::Extern(..)
        | Prim::AllocStruct(..)
        | Prim::ListCons(..)
        | Prim::ListHead(..)
        | Prim::ListTail(..)
        | Prim::MakeList(..)
        | Prim::MakeMap(..)
        | Prim::MapUpdate(..)
        | Prim::MapGet(..)
        | Prim::MakeVec(..)
        | Prim::MakeBitstring(..)
        | Prim::ConstBitstring(..)
        | Prim::BitReaderInit(..)
        | Prim::BitReadField { .. }
        | Prim::BitReaderDone(..) => None,
        // fz-axu.23 (M2) — lower_program_full erases Prim::Brand
        // before the reducer runs. Surface a stray Brand instead of
        // silently re-introducing brand-transparent fold logic.
        Prim::Brand(_, _) => unreachable!(
            "Prim::Brand reached reducer — erasure should run inside lower_program_full"
        ),
    }
}

fn fold_const<T: Types>(t: &mut T, c: &Const, atom_names: &[String]) -> Option<T::Ty> {
    let d = match c {
        Const::Int(n) => Descr::int_lit(*n),
        Const::Float(f) => Descr::float_lit(*f),
        Const::Nil => Descr::nil(),
        Const::True => Descr::atom_lit("true"),
        Const::False => Descr::atom_lit("false"),
        Const::Atom(id) => {
            let name = atom_names.get(*id as usize)?;
            Descr::atom_lit(name)
        }
    };
    Some(t.from_descr(&d))
}

fn fold_binop<T: Types>(
    t: &mut T,
    op: BinOp,
    a: Var,
    b: Var,
    env: &HashMap<Var, Descr>,
) -> Option<T::Ty> {
    let ad = env.get(&a)?;
    let bd = env.get(&b)?;
    use BinOp::*;
    let d = match op {
        Add | Sub | Mul | Div | Mod => fold_arith(op, ad, bd),
        Eq | Neq => fold_eq(op, ad, bd),
        Lt | Le | Gt | Ge => fold_cmp(op, ad, bd),
        And | Or => fold_logical(op, ad, bd),
    }?;
    Some(t.from_descr(&d))
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
        return Some(bool_descr(!is_eq));
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
            Ge => af >= bf,
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

fn fold_unop<T: Types>(
    t: &mut T,
    op: UnOp,
    v: Var,
    env: &HashMap<Var, Descr>,
) -> Option<T::Ty> {
    let d = env.get(&v)?;
    let r: Descr = match op {
        UnOp::Neg => {
            if let Some(n) = as_int_lit(d) {
                Descr::int_lit(n.checked_neg()?)
            } else if let Some(f) = as_float_lit(d) {
                Descr::float_lit(-f.get())
            } else {
                return None;
            }
        }
        UnOp::Not => bool_descr(!as_bool_lit(d)?),
    };
    Some(t.from_descr(&r))
}

fn fold_make_tuple<T: Types>(
    t: &mut T,
    vs: &[Var],
    env: &HashMap<Var, Descr>,
) -> Option<T::Ty> {
    let mut elems = Vec::with_capacity(vs.len());
    for v in vs {
        let d = env.get(v)?;
        if !is_literal(d) {
            return None;
        }
        elems.push(d.clone());
    }
    Some(t.from_descr(&Descr::tuple_of(elems)))
}

fn fold_tuple_field<T: Types>(
    t: &mut T,
    v: Var,
    i: usize,
    env: &HashMap<Var, Descr>,
) -> Option<T::Ty> {
    let d = env.get(&v)?;
    let elems = as_tuple_lit(d)?;
    Some(t.from_descr(elems.get(i)?))
}

fn fold_type_test<T: Types>(
    t: &mut T,
    v: Var,
    descr: &Descr,
    env: &HashMap<Var, Descr>,
) -> Option<T::Ty> {
    let vd = env.get(&v)?;
    let r = if vd.is_subtype(descr) {
        bool_descr(true)
    } else if vd.intersect(descr).is_empty() {
        bool_descr(false)
    } else {
        return None;
    };
    Some(t.from_descr(&r))
}

/// fz-jg5.6: produce a `closure_lit(F, [literal captures])` Descr when
/// every captured Var has a literal Descr in `env`. The reducer then
/// dispatches calls through this closure to `F` directly.
fn fold_make_closure<T: Types>(
    t: &mut T,
    fn_id: crate::fz_ir::FnId,
    captured: &[Var],
    env: &HashMap<Var, Descr>,
) -> Option<T::Ty> {
    let mut cap_descrs: Vec<Descr> = Vec::with_capacity(captured.len());
    for cv in captured {
        let d = env.get(cv)?.clone();
        if !is_literal(&d) {
            return None;
        }
        cap_descrs.push(d);
    }
    // n_args is the closure's apparent post-capture arity. We don't
    // know it here without consulting Module.fn_by_id; passing 0 means
    // downstream consumers must look up the body's true arity. The
    // reducer's call-dispatch path consults the body directly, so this
    // 0 placeholder is fine.
    Some(t.from_descr(&Descr::closure_lit(fn_id, cap_descrs, 0)))
}

fn fold_list_is_nil<T: Types>(
    t: &mut T,
    v: Var,
    env: &HashMap<Var, Descr>,
) -> Option<T::Ty> {
    let d = env.get(&v)?;
    // fz-yan.1 — post-fz-s9y, `nil` (the atom) and `[]` (the empty list
    // sentinel) are distinct bit patterns. `IsEmptyList` tests for the
    // EMPTY_LIST sentinel, so a value provably equal to `nil` folds to
    // `false`, not `true` as it did pre-s9y. The `list_of(none())` case
    // — i.e. provably the empty list — still folds to `true`.
    if is_nil_only(d) {
        Some(t.from_descr(&bool_descr(false)))
    } else if d.intersect(&Descr::nil()).is_empty()
        && d.components()
            .any(|c| matches!(c, crate::types::Component::Lists(_)))
    {
        // Disjoint from `nil` and has a non-empty `lists` axis: this is
        // either `[]` or a cons. Without a finer "non-empty list" track
        // in the lattice we can't separate the two, so we leave the
        // fold to the runtime.
        None
    } else {
        None
    }
}

fn bool_descr(b: bool) -> Descr {
    Descr::atom_lit(if b { "true" } else { "false" })
}

// ---------------------------------------------------------------------------
// fz-jg5.3 (RED.2) — Clause dispatch via pattern matrix
// ---------------------------------------------------------------------------

/// A clause for the reducer's dispatcher. Mirrors `pattern_matrix::Row` but
/// is matrix-uniform — usable for fn-clauses, `case`, and `with` matrices.
#[allow(dead_code)] // wired by RED.4+ when the reducer can dispatch multi-clause fns at AST level.
pub struct Clause<'a> {
    /// One pattern per subject. `patterns.len()` must equal the dispatcher's
    /// `subject_descrs.len()`.
    pub patterns: &'a [Spanned<Pattern>],
    /// Optional guard. Evaluated under the row's bindings; must fold to a
    /// bool literal for the clause to be selected statically.
    pub guard: Option<&'a Spanned<ast::Expr>>,
}

/// Outcome of dispatching a list of clauses against subject Descrs.
#[derive(Debug, Clone)]
#[allow(dead_code)] // wired by RED.4+.
pub enum Dispatch {
    /// `row_idx` is the lowest-index row whose patterns and guard match
    /// the subject Descrs (first-match-wins). `bindings` carries the
    /// source-name → literal-Descr map the row's body sees.
    MatchedRow {
        row_idx: usize,
        bindings: HashMap<String, Descr>,
    },
    /// Every row has provably-disjoint patterns or a provably-false guard.
    /// Runtime would raise function_clause / match_error. The reducer
    /// should leave the call in place.
    NoMatch,
    /// Cannot statically pick a row. Reducer emits a body for the callee.
    Opaque,
}

/// First-match-wins dispatch of `clauses` against `subject_descrs`.
///
/// Algorithm:
/// - For each row in source order, try to match every pattern against the
///   corresponding subject Descr (`match_pattern`).
/// - If all patterns match and the guard (if any) folds to `true`, return
///   `MatchedRow`.
/// - If any pattern is provably-disjoint, OR a guard folds to `false`,
///   skip the row.
/// - If any pattern OR the guard is indeterminate (Opaque), return Opaque
///   immediately — we cannot prove this row is OR isn't selected; trying
///   later rows would be unsound since this row might match at runtime.
/// - If every row is skipped (NoMatch), return NoMatch.
#[allow(dead_code)] // wired by RED.4+.
pub fn dispatch_clauses<T: Types>(
    t: &mut T,
    clauses: &[Clause<'_>],
    subject_descrs: &[Descr],
    atom_names: &[String],
) -> Dispatch {
    for (idx, row) in clauses.iter().enumerate() {
        if row.patterns.len() != subject_descrs.len() {
            return Dispatch::Opaque; // arity mismatch is the caller's bug
        }
        let mut bindings: HashMap<String, Descr> = HashMap::new();
        let mut all_match = true;
        let mut row_opaque = false;
        for (pat, d) in row.patterns.iter().zip(subject_descrs.iter()) {
            match match_pattern(&pat.node, d, &mut bindings, atom_names) {
                Match::Yes => {}
                Match::No => {
                    all_match = false;
                    break;
                }
                Match::Opaque => {
                    row_opaque = true;
                    break;
                }
            }
        }
        if row_opaque {
            return Dispatch::Opaque;
        }
        if !all_match {
            continue;
        }
        // Patterns matched — try guard.
        if let Some(guard) = row.guard {
            match fold_expr(t, &guard.node, &bindings, atom_names) {
                Some(d) => match as_bool_lit(&d.as_descr()) {
                    Some(true) => {
                        return Dispatch::MatchedRow {
                            row_idx: idx,
                            bindings,
                        };
                    }
                    Some(false) => continue, // guard rejects row; try next
                    None => return Dispatch::Opaque, // guard folded but not to bool — give up
                },
                None => return Dispatch::Opaque, // guard didn't fold
            }
        }
        return Dispatch::MatchedRow {
            row_idx: idx,
            bindings,
        };
    }
    Dispatch::NoMatch
}

#[derive(Debug, Clone, Copy)]
enum Match {
    Yes,
    No,
    Opaque,
}

/// Match a single AST `Pattern` against a subject `Descr`. On `Match::Yes`,
/// any `Pattern::Var(name)` and `Pattern::As(name, _)` records bind `name`
/// to the (sub-)Descr of the subject.
#[allow(dead_code)] // helpers for dispatch_clauses.
fn match_pattern(
    pat: &Pattern,
    d: &Descr,
    bindings: &mut HashMap<String, Descr>,
    atom_names: &[String],
) -> Match {
    use Pattern::*;
    match pat {
        Wildcard => Match::Yes,
        Var(name) => {
            bindings.insert(name.clone(), d.clone());
            Match::Yes
        }
        As(name, inner) => {
            bindings.insert(name.clone(), d.clone());
            match_pattern(&inner.node, d, bindings, atom_names)
        }
        Int(n) => match_literal(d, &Descr::int_lit(*n)),
        Float(f) => match_literal(d, &Descr::float_lit(*f)),
        Str(_) => {
            // Post-fz-axu.11 (L3) lowers Pattern::Str to a bitstring/brand
            // check at the IR level. The AST evaluator never sees a
            // singleton string Descr to match against, so defer to the
            // IR-level reducer.
            Match::Opaque
        }
        Atom(name) => match_literal(d, &Descr::atom_lit(name)),
        Bool(b) => match_literal(d, &Descr::atom_lit(if *b { "true" } else { "false" })),
        Nil => match_literal(d, &Descr::nil()),
        Tuple(elems) => match_tuple_pattern(elems, d, bindings, atom_names),
        // List patterns require IR-level reasoning (lists' Descrs lose length
        // information — see RED.1 note). Return Opaque so the reducer keeps
        // the call; RED.3+ may extend this.
        List(_, _) => Match::Opaque,
        // Map and Bitstring patterns: defer to a per-row IR-walking fallback
        // (the matrix's `PerRow` decision) — for the reducer, treat as opaque.
        Map(_) | Bitstring(_) => Match::Opaque,
        // fz-5vj — `^name` compares against an outer binding's runtime value.
        // The reducer doesn't see runtime values, so this is always Opaque.
        Pinned(_) => Match::Opaque,
    }
}

/// A pattern that demands a specific literal value. Returns Yes if `d` is
/// equal to `expected` (both are singleton-literal of the same shape), No if
/// they're disjoint, Opaque otherwise.
#[allow(dead_code)]
fn match_literal(d: &Descr, expected: &Descr) -> Match {
    if is_literal(d) {
        if d == expected {
            Match::Yes
        } else if d.intersect(expected).is_empty() {
            Match::No
        } else {
            // Both literal but not equal yet not disjoint — shouldn't happen
            // for the literal forms we support. Be conservative.
            Match::Opaque
        }
    } else if d.intersect(expected).is_empty() {
        Match::No
    } else if d.is_subtype(expected) {
        // Subject's Descr is narrower than `expected` and contained — match.
        Match::Yes
    } else {
        Match::Opaque
    }
}

#[allow(dead_code)]
fn match_tuple_pattern(
    elems: &[Spanned<Pattern>],
    d: &Descr,
    bindings: &mut HashMap<String, Descr>,
    atom_names: &[String],
) -> Match {
    // Need d to be a single-shape tuple (one positive clause, one sig, no
    // negations, no other axes populated). Elements need NOT be literal —
    // they can be wide Descrs matched by Var/Wildcard.
    //
    // If d admits no tuples at all, it's a definite No. If it admits tuples
    // but not as a single shape (multi-clause, mixed axes, negations), it's
    // Opaque.
    use crate::types::Component;
    let admits_tuple = d.components().any(|c| matches!(c, Component::Tuples(_)));
    let Some(sig_elems) = d.as_tuple_singleton() else {
        return if admits_tuple {
            Match::Opaque
        } else {
            Match::No
        };
    };
    if sig_elems.len() != elems.len() {
        return Match::No;
    }
    let mut saw_opaque = false;
    for (p, ed) in elems.iter().zip(sig_elems.iter()) {
        match match_pattern(&p.node, ed, bindings, atom_names) {
            Match::Yes => {}
            Match::No => return Match::No,
            Match::Opaque => saw_opaque = true,
        }
    }
    if saw_opaque {
        Match::Opaque
    } else {
        Match::Yes
    }
}

/// Fold an AST `Expr` to a literal Descr under `bindings`. Used for guards.
/// Conservative — handles Var lookup, scalar literals, BinOp, UnOp.
/// Anything else returns None (Opaque guard).
#[allow(dead_code)]
// pub for fz-jg5.3's dispatcher; called by fold_expr; main bin's call graph doesn't reach it yet (RED.3+).
#[allow(clippy::only_used_in_recursion)] // atom_names threaded for API symmetry with siblings; future Expr arms may consult it.
pub fn fold_expr<T: Types>(
    t: &mut T,
    expr: &ast::Expr,
    bindings: &HashMap<String, Descr>,
    atom_names: &[String],
) -> Option<T::Ty> {
    use ast::Expr;
    let d = match expr {
        Expr::Var(name) => bindings.get(name).cloned(),
        Expr::Int(n) => Some(Descr::int_lit(*n)),
        Expr::Float(f) => Some(Descr::float_lit(*f)),
        Expr::Str(_) => {
            // Post-fz-axu.11 (L3) lowers Expr::Str at the IR level to a
            // bitstring+brand. No singleton Descr representation remains,
            // so AST-level folding gives up here.
            None
        }
        Expr::Atom(s) => Some(Descr::atom_lit(s)),
        Expr::Bool(b) => Some(bool_descr(*b)),
        Expr::Nil => Some(Descr::nil()),
        Expr::BinOp(op, a, b) => {
            let ad = fold_expr(t, &a.node, bindings, atom_names)?.as_descr();
            let bd = fold_expr(t, &b.node, bindings, atom_names)?.as_descr();
            ast_binop_fold(t, *op, &ad, &bd)
        }
        Expr::UnOp(op, v) => {
            let vd = fold_expr(t, &v.node, bindings, atom_names)?.as_descr();
            ast_unop_fold(t, *op, &vd)
        }
        _ => None,
    }?;
    Some(t.from_descr(&d))
}

#[allow(dead_code)] // used via fold_expr; cf. RED.3+ wiring.
fn ast_binop_fold<T: Types>(_t: &mut T, op: ast::BinOp, ad: &Descr, bd: &Descr) -> Option<Descr> {
    use ast::BinOp::*;
    let ir_op = match op {
        Add => BinOp::Add,
        Sub => BinOp::Sub,
        Mul => BinOp::Mul,
        Div => BinOp::Div,
        Rem => BinOp::Mod,
        Eq => BinOp::Eq,
        Neq => BinOp::Neq,
        Lt => BinOp::Lt,
        LtEq => BinOp::Le,
        Gt => BinOp::Gt,
        GtEq => BinOp::Ge,
        And => BinOp::And,
        Or => BinOp::Or,
        // Pipe and Cons aren't fold-prim-able in the same shape.
        Pipe | Cons => return None,
    };
    match ir_op {
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => fold_arith(ir_op, ad, bd),
        BinOp::Eq | BinOp::Neq => fold_eq(ir_op, ad, bd),
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => fold_cmp(ir_op, ad, bd),
        BinOp::And | BinOp::Or => fold_logical(ir_op, ad, bd),
    }
}

#[allow(dead_code)] // used via fold_expr.
fn ast_unop_fold<T: Types>(_t: &mut T, op: ast::UnOp, d: &Descr) -> Option<Descr> {
    use ast::UnOp::*;
    let ir_op = match op {
        Neg => UnOp::Neg,
        Not => UnOp::Not,
    };
    match ir_op {
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

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::Var;
    use crate::types_seam::{AsDescr, ConcreteTypes};

    fn ct() -> ConcreteTypes {
        ConcreteTypes
    }

    fn v(n: u32) -> Var {
        Var(n)
    }

    fn env(pairs: &[(u32, Descr)]) -> HashMap<Var, Descr> {
        pairs.iter().map(|(i, d)| (Var(*i), d.clone())).collect()
    }

    // ---- is_literal predicates ----

    #[test]
    #[allow(clippy::approx_constant)] // 3.14 here is just a float literal, not π.
    fn is_literal_recognizes_scalar_singletons() {
        assert!(is_literal(&Descr::int_lit(42)));
        assert!(is_literal(&Descr::float_lit(3.14)));
        assert!(is_literal(&Descr::atom_lit("foo")));
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
        let r = fold_prim(&mut ct(), &Prim::Const(Const::Int(42)), &HashMap::new(), &[]).unwrap().as_descr();
        assert_eq!(as_int_lit(&r), Some(42));
    }

    #[test]
    fn fold_const_nil_and_bools() {
        let nil = fold_prim(&mut ct(), &Prim::Const(Const::Nil), &HashMap::new(), &[]).unwrap().as_descr();
        assert!(is_nil_only(&nil));
        let t = fold_prim(&mut ct(), &Prim::Const(Const::True), &HashMap::new(), &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&t), Some(true));
        let f = fold_prim(&mut ct(), &Prim::Const(Const::False), &HashMap::new(), &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&f), Some(false));
    }

    #[test]
    fn fold_const_atom_uses_atom_table() {
        let names = vec!["alpha".to_string(), "beta".to_string()];
        let a = fold_prim(&mut ct(), &Prim::Const(Const::Atom(1)), &HashMap::new(), &names).unwrap().as_descr();
        assert_eq!(as_atom_lit(&a), Some("beta"));
    }

    #[test]
    fn fold_const_atom_out_of_range_returns_none() {
        let names: Vec<String> = vec![];
        assert!(fold_prim(&mut ct(), &Prim::Const(Const::Atom(0)), &HashMap::new(), &names).is_none());
    }

    // ---- arithmetic ----

    #[test]
    fn fold_int_add() {
        let env = env(&[(0, Descr::int_lit(41)), (1, Descr::int_lit(1))]);
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_int_lit(&r), Some(42));
    }

    #[test]
    fn fold_int_div_by_zero_returns_none() {
        let env = env(&[(0, Descr::int_lit(10)), (1, Descr::int_lit(0))]);
        assert!(fold_prim(&mut ct(), &Prim::BinOp(BinOp::Div, v(0), v(1)), &env, &[]).is_none());
    }

    #[test]
    fn fold_int_overflow_returns_none() {
        let env = env(&[(0, Descr::int_lit(i64::MAX)), (1, Descr::int_lit(1))]);
        assert!(fold_prim(&mut ct(), &Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).is_none());
    }

    #[test]
    fn fold_float_arith() {
        let env = env(&[(0, Descr::float_lit(1.5)), (1, Descr::float_lit(2.5))]);
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_float_lit(&r).map(|f| f.get()), Some(4.0));
    }

    #[test]
    fn fold_mixed_int_float_returns_none() {
        // No coercion; the typer's policy is no auto-promotion.
        let env = env(&[(0, Descr::int_lit(1)), (1, Descr::float_lit(2.0))]);
        assert!(fold_prim(&mut ct(), &Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).is_none());
    }

    #[test]
    fn fold_arith_on_wide_input_returns_none() {
        let env = env(&[(0, Descr::int()), (1, Descr::int_lit(1))]);
        assert!(fold_prim(&mut ct(), &Prim::BinOp(BinOp::Add, v(0), v(1)), &env, &[]).is_none());
    }

    // ---- comparison ----

    #[test]
    fn fold_int_lt() {
        let env = env(&[(0, Descr::int_lit(1)), (1, Descr::int_lit(2))]);
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::Lt, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    // ---- equality + kind-disjoint fold ----

    #[test]
    fn fold_eq_literal_match() {
        let env = env(&[(0, Descr::int_lit(42)), (1, Descr::int_lit(42))]);
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::Eq, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    #[test]
    fn fold_eq_literal_mismatch() {
        let env = env(&[(0, Descr::int_lit(42)), (1, Descr::int_lit(7))]);
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::Eq, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(false));
    }

    #[test]
    fn fold_neq_literal_mismatch_is_true() {
        let env = env(&[(0, Descr::int_lit(42)), (1, Descr::int_lit(7))]);
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::Neq, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    #[test]
    fn fold_eq_kind_disjoint_non_literal() {
        // int vs atom_top: kinds disjoint at the lattice level.
        // VR.5a's case — fold to false even though operands aren't literal.
        let env = env(&[(0, Descr::int()), (1, Descr::atom_top())]);
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::Eq, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(false));
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::Neq, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    #[test]
    fn fold_eq_overlapping_non_literal_returns_none() {
        // int vs int: kinds overlap; cannot decide statically.
        let env = env(&[(0, Descr::int()), (1, Descr::int())]);
        assert!(fold_prim(&mut ct(), &Prim::BinOp(BinOp::Eq, v(0), v(1)), &env, &[]).is_none());
    }

    // ---- logical ----

    #[test]
    fn fold_and_bool_lits() {
        let env = env(&[(0, Descr::atom_lit("true")), (1, Descr::atom_lit("false"))]);
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::And, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(false));
        let env = env_with_true();
        let r = fold_prim(&mut ct(), &Prim::BinOp(BinOp::Or, v(0), v(1)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    fn env_with_true() -> HashMap<Var, Descr> {
        env(&[(0, Descr::atom_lit("true")), (1, Descr::atom_lit("false"))])
    }

    // ---- unary ----

    #[test]
    fn fold_neg_int() {
        let env = env(&[(0, Descr::int_lit(5))]);
        let r = fold_prim(&mut ct(), &Prim::UnOp(UnOp::Neg, v(0)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_int_lit(&r), Some(-5));
    }

    #[test]
    fn fold_not_bool() {
        let env = env(&[(0, Descr::atom_lit("true"))]);
        let r = fold_prim(&mut ct(), &Prim::UnOp(UnOp::Not, v(0)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(false));
    }

    // ---- tuple ----

    #[test]
    fn fold_make_tuple_of_literals() {
        let env = env(&[(0, Descr::atom_lit("num")), (1, Descr::int_lit(42))]);
        let r = fold_prim(&mut ct(), &Prim::MakeTuple(vec![v(0), v(1)]), &env, &[]).unwrap().as_descr();
        let elems = as_tuple_lit(&r).unwrap();
        assert_eq!(elems.len(), 2);
        assert_eq!(as_atom_lit(&elems[0]), Some("num"));
        assert_eq!(as_int_lit(&elems[1]), Some(42));
    }

    #[test]
    fn fold_make_tuple_with_wide_element_is_none() {
        let env = env(&[(0, Descr::atom_lit("num")), (1, Descr::int())]);
        assert!(fold_prim(&mut ct(), &Prim::MakeTuple(vec![v(0), v(1)]), &env, &[]).is_none());
    }

    #[test]
    fn fold_tuple_field_literal() {
        let t = Descr::tuple_of([Descr::atom_lit("num"), Descr::int_lit(42)]);
        let env = env(&[(0, t)]);
        let r = fold_prim(&mut ct(), &Prim::TupleField(v(0), 1), &env, &[]).unwrap().as_descr();
        assert_eq!(as_int_lit(&r), Some(42));
        let r = fold_prim(&mut ct(), &Prim::TupleField(v(0), 0), &env, &[]).unwrap().as_descr();
        assert_eq!(as_atom_lit(&r), Some("num"));
    }

    #[test]
    fn fold_tuple_field_out_of_range() {
        let t = Descr::tuple_of([Descr::atom_lit("num"), Descr::int_lit(42)]);
        let env = env(&[(0, t)]);
        assert!(fold_prim(&mut ct(), &Prim::TupleField(v(0), 7), &env, &[]).is_none());
    }

    // ---- type test ----

    #[test]
    fn fold_type_test_proves_true() {
        let env = env(&[(0, Descr::int_lit(42))]);
        let r = fold_prim(&mut ct(), &Prim::TypeTest(v(0), Box::new(Descr::int())), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(true));
    }

    #[test]
    fn fold_type_test_proves_false() {
        let env = env(&[(0, Descr::int_lit(42))]);
        let r = fold_prim(&mut ct(), 
            &Prim::TypeTest(v(0), Box::new(Descr::atom_top())),
            &env,
            &[],
        )
        .unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(false));
    }

    #[test]
    fn fold_type_test_undecidable_returns_none() {
        let env = env(&[(0, Descr::any())]);
        assert!(fold_prim(&mut ct(), &Prim::TypeTest(v(0), Box::new(Descr::int())), &env, &[]).is_none());
    }

    // ---- list_is_nil ----

    #[test]
    fn fold_list_is_nil_on_nil() {
        // fz-yan.1 — post-fz-s9y, `nil` ≠ `[]`. A provably-nil value is
        // NOT the empty-list sentinel, so IsEmptyList folds to `false`.
        let env = env(&[(0, Descr::nil())]);
        let r = fold_prim(&mut ct(), &Prim::IsEmptyList(v(0)), &env, &[]).unwrap().as_descr();
        assert_eq!(as_bool_lit(&r), Some(false));
    }

    #[test]
    fn fold_list_is_nil_on_list_of_int_is_unknown() {
        // fz-yan.1 — post-fz-s9y, `list_of(int)` includes the empty list,
        // so we can no longer fold to `false`. Leave the test to runtime.
        let env = env(&[(0, Descr::list_of(Descr::int_lit(1)))]);
        assert!(fold_prim(&mut ct(), &Prim::IsEmptyList(v(0)), &env, &[]).is_none());
    }

    #[test]
    fn fold_list_is_nil_on_maybe_empty_returns_none() {
        // list_of(int) | nil — could be either.
        let env = env(&[(0, Descr::list_of(Descr::int_lit(1)).union(&Descr::nil()))]);
        assert!(fold_prim(&mut ct(), &Prim::IsEmptyList(v(0)), &env, &[]).is_none());
    }

    // ---- non-foldable prims explicitly return None ----

    #[test]
    fn fold_extern_returns_none() {
        use crate::fz_ir::ExternId;
        let env = HashMap::new();
        assert!(fold_prim(&mut ct(), &Prim::Extern(ExternId(0), vec![]), &env, &[],).is_none());
    }

    #[test]
    fn fold_make_list_returns_none() {
        // Lists are folded by IR-walking in RED.3+, not by fold_prim.
        let env = env(&[(0, Descr::int_lit(1)), (1, Descr::int_lit(2))]);
        assert!(fold_prim(&mut ct(), &Prim::MakeList(vec![v(0), v(1)], None), &env, &[]).is_none());
    }

    // Bitstring construction / reader prims aren't foldable in v1; covered
    // by the explicit None-returning match arms in `fold_prim`. ConstBitstring
    // and friends are exercised by the wider codegen tests, not here.

    // ============================================================
    // fz-jg5.3 — Dispatch tests
    // ============================================================

    use crate::ast::{Expr, Pattern, Spanned};

    fn pat(p: Pattern) -> Spanned<Pattern> {
        Spanned::dummy(p)
    }

    fn expr(e: Expr) -> Spanned<Expr> {
        Spanned::dummy(e)
    }

    // ---- single-clause matching ----

    #[test]
    fn dispatch_wildcard_always_matches() {
        let patterns = vec![pat(Pattern::Wildcard)];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::any()], &[]);
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 0, .. }));
    }

    #[test]
    fn dispatch_var_binds_subject_descr() {
        let patterns = vec![pat(Pattern::Var("n".to_string()))];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::int_lit(42)], &[]);
        match result {
            Dispatch::MatchedRow {
                row_idx: 0,
                bindings,
            } => {
                assert_eq!(as_int_lit(bindings.get("n").unwrap()), Some(42));
            }
            other => panic!("expected MatchedRow, got {:?}", other),
        }
    }

    #[test]
    fn dispatch_int_literal_match() {
        let patterns = vec![pat(Pattern::Int(0))];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::int_lit(0)], &[]);
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 0, .. }));
    }

    #[test]
    fn dispatch_int_literal_no_match() {
        let patterns = vec![pat(Pattern::Int(0))];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::int_lit(7)], &[]);
        assert!(matches!(result, Dispatch::NoMatch));
    }

    #[test]
    fn dispatch_int_literal_opaque_against_wide_int() {
        // Literal pattern against wide int Descr — indeterminate at compile time.
        let patterns = vec![pat(Pattern::Int(0))];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::int()], &[]);
        assert!(matches!(result, Dispatch::Opaque));
    }

    // ---- multi-clause dispatch (ast_eval-shape) ----

    #[test]
    fn dispatch_ast_eval_num_clause() {
        // Three clauses of eval, simplified: {:num,n} / {:add,a,b} / {:mul,a,b}.
        let num_pat = pat(Pattern::Tuple(vec![
            pat(Pattern::Atom("num".to_string())),
            pat(Pattern::Var("n".to_string())),
        ]));
        let add_pat = pat(Pattern::Tuple(vec![
            pat(Pattern::Atom("add".to_string())),
            pat(Pattern::Var("a".to_string())),
            pat(Pattern::Var("b".to_string())),
        ]));
        let mul_pat = pat(Pattern::Tuple(vec![
            pat(Pattern::Atom("mul".to_string())),
            pat(Pattern::Var("a".to_string())),
            pat(Pattern::Var("b".to_string())),
        ]));
        let clause_num = vec![num_pat.clone()];
        let clause_add = vec![add_pat];
        let clause_mul = vec![mul_pat];
        let clauses = vec![
            Clause {
                patterns: &clause_num,
                guard: None,
            },
            Clause {
                patterns: &clause_add,
                guard: None,
            },
            Clause {
                patterns: &clause_mul,
                guard: None,
            },
        ];

        let subject = Descr::tuple_of([Descr::atom_lit("num"), Descr::int_lit(42)]);
        match dispatch_clauses(&mut ct(), &clauses, &[subject], &[]) {
            Dispatch::MatchedRow { row_idx, bindings } => {
                assert_eq!(row_idx, 0);
                assert_eq!(as_int_lit(bindings.get("n").unwrap()), Some(42));
            }
            other => panic!("expected num-clause match, got {:?}", other),
        }
    }

    #[test]
    fn dispatch_ast_eval_add_clause() {
        let num_pat = pat(Pattern::Tuple(vec![
            pat(Pattern::Atom("num".to_string())),
            pat(Pattern::Var("n".to_string())),
        ]));
        let add_pat = pat(Pattern::Tuple(vec![
            pat(Pattern::Atom("add".to_string())),
            pat(Pattern::Var("a".to_string())),
            pat(Pattern::Var("b".to_string())),
        ]));
        let c0 = vec![num_pat];
        let c1 = vec![add_pat];
        let clauses = vec![
            Clause {
                patterns: &c0,
                guard: None,
            },
            Clause {
                patterns: &c1,
                guard: None,
            },
        ];

        let inner_a = Descr::tuple_of([Descr::atom_lit("num"), Descr::int_lit(2)]);
        let inner_b = Descr::tuple_of([Descr::atom_lit("num"), Descr::int_lit(3)]);
        let subject = Descr::tuple_of([Descr::atom_lit("add"), inner_a.clone(), inner_b.clone()]);
        match dispatch_clauses(&mut ct(), &clauses, &[subject], &[]) {
            Dispatch::MatchedRow { row_idx, bindings } => {
                assert_eq!(row_idx, 1);
                assert_eq!(bindings.get("a").unwrap(), &inner_a);
                assert_eq!(bindings.get("b").unwrap(), &inner_b);
            }
            other => panic!("expected add-clause match, got {:?}", other),
        }
    }

    #[test]
    fn dispatch_ast_eval_opaque_on_any() {
        let num_pat = pat(Pattern::Tuple(vec![
            pat(Pattern::Atom("num".to_string())),
            pat(Pattern::Var("n".to_string())),
        ]));
        let c0 = vec![num_pat];
        let clauses = vec![Clause {
            patterns: &c0,
            guard: None,
        }];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::any()], &[]);
        assert!(matches!(result, Dispatch::Opaque));
    }

    // ---- first-match-wins (wildcard_then_specific) ----

    #[test]
    fn dispatch_first_match_wins_over_specific() {
        // Wildcard clause first, then a specific clause that would also match —
        // wildcard wins per source order.
        let wild = vec![pat(Pattern::Wildcard)];
        let specific = vec![pat(Pattern::Int(0))];
        let clauses = vec![
            Clause {
                patterns: &wild,
                guard: None,
            },
            Clause {
                patterns: &specific,
                guard: None,
            },
        ];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::int_lit(0)], &[]);
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 0, .. }));
    }

    // ---- guard handling (multi_clause-shape) ----

    #[test]
    fn dispatch_guard_true_selects_clause() {
        // classify(n) when n > 0 — bind n := 7, guard `n > 0` folds to true.
        let p = vec![pat(Pattern::Var("n".to_string()))];
        let guard = expr(Expr::BinOp(
            ast::BinOp::Gt,
            Box::new(expr(Expr::Var("n".to_string()))),
            Box::new(expr(Expr::Int(0))),
        ));
        let clauses = vec![Clause {
            patterns: &p,
            guard: Some(&guard),
        }];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::int_lit(7)], &[]);
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 0, .. }));
    }

    #[test]
    fn dispatch_guard_false_skips_clause() {
        // Two clauses: first with `n > 0` guard, second without.
        // Subject n := -3 — guard fails, second clause selected.
        let p0 = vec![pat(Pattern::Var("n".to_string()))];
        let p1 = vec![pat(Pattern::Var("n".to_string()))];
        let guard = expr(Expr::BinOp(
            ast::BinOp::Gt,
            Box::new(expr(Expr::Var("n".to_string()))),
            Box::new(expr(Expr::Int(0))),
        ));
        let clauses = vec![
            Clause {
                patterns: &p0,
                guard: Some(&guard),
            },
            Clause {
                patterns: &p1,
                guard: None,
            },
        ];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::int_lit(-3)], &[]);
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 1, .. }));
    }

    #[test]
    fn dispatch_guard_indeterminate_returns_opaque() {
        // Guard refers to n :: int (wide); cannot fold. Opaque.
        let p = vec![pat(Pattern::Var("n".to_string()))];
        let guard = expr(Expr::BinOp(
            ast::BinOp::Gt,
            Box::new(expr(Expr::Var("n".to_string()))),
            Box::new(expr(Expr::Int(0))),
        ));
        let clauses = vec![Clause {
            patterns: &p,
            guard: Some(&guard),
        }];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::int()], &[]);
        assert!(matches!(result, Dispatch::Opaque));
    }

    // ---- list patterns are opaque in v1 ----

    #[test]
    fn dispatch_list_pattern_opaque() {
        let pat_list = vec![pat(Pattern::List(vec![pat(Pattern::Wildcard)], None))];
        let clauses = vec![Clause {
            patterns: &pat_list,
            guard: None,
        }];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::list_of(Descr::int_lit(1))], &[]);
        assert!(matches!(result, Dispatch::Opaque));
    }

    // ---- As-patterns ----

    #[test]
    fn dispatch_as_pattern_binds_outer_and_matches_inner() {
        // `whole = {:num, n}` — bind `whole` to the tuple, `n` to the int.
        let inner = pat(Pattern::Tuple(vec![
            pat(Pattern::Atom("num".to_string())),
            pat(Pattern::Var("n".to_string())),
        ]));
        let outer = vec![pat(Pattern::As("whole".to_string(), Box::new(inner)))];
        let clauses = vec![Clause {
            patterns: &outer,
            guard: None,
        }];
        let subject = Descr::tuple_of([Descr::atom_lit("num"), Descr::int_lit(42)]);
        match dispatch_clauses(&mut ct(), &clauses, std::slice::from_ref(&subject), &[]) {
            Dispatch::MatchedRow { bindings, .. } => {
                assert_eq!(bindings.get("whole").unwrap(), &subject);
                assert_eq!(as_int_lit(bindings.get("n").unwrap()), Some(42));
            }
            other => panic!("expected match, got {:?}", other),
        }
    }

    // ---- no-match across multiple clauses ----

    #[test]
    fn dispatch_no_match_when_every_clause_disjoint() {
        // Three clauses each demanding specific int literals; subject is a
        // different int literal.
        let p0 = vec![pat(Pattern::Int(0))];
        let p1 = vec![pat(Pattern::Int(1))];
        let p2 = vec![pat(Pattern::Int(2))];
        let clauses = vec![
            Clause {
                patterns: &p0,
                guard: None,
            },
            Clause {
                patterns: &p1,
                guard: None,
            },
            Clause {
                patterns: &p2,
                guard: None,
            },
        ];
        let result = dispatch_clauses(&mut ct(), &clauses, &[Descr::int_lit(7)], &[]);
        assert!(matches!(result, Dispatch::NoMatch));
    }
}
