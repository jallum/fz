//! fz-jg5.2 (RED.1) — Pattern reduction primitive.
//!
//! Pure functions used by the compile-time reducer (RED.3+).
//! `fold_prim` takes a `Prim` and an `env` of (Var → Ty) and returns
//! `Some(literal_ty)` when the Prim's output is uniquely determined,
//! `None` otherwise.
//!
//! Scope: scalars, tuples, closures, and TypeTest. List-structure folding
//! (e.g. ListHead/ListTail on a 5-element literal list) is NOT handled
//! here because list types (`list_of(elem)`) lose length information —
//! that case wants IR-walking, which lands in RED.3.
//!
//! See `docs/walkthroughs/FINDINGS.md` for the refined rule set this
//! module embodies. In particular: kind-disjoint Eq/Neq folds even on
//! non-literal operands; `closure_lit(F, [literal captures])` is a
//! first-class literal type.

use crate::ast::{self, Pattern, Spanned};
use crate::fz_ir::{BinOp, Const, Prim, UnOp, Var};
use crate::types::{LiteralTypes, Nominals, Types};
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// fold_prim
// ---------------------------------------------------------------------------

/// If the Prim's output is uniquely determined under `env`, return the
/// literal type. Otherwise None.
///
/// `atom_names` is the module's atom interner; `Const::Atom(id)` resolves
/// to `atom_lit(atom_names[id])`. Pass `&[]` if unused (Const::Atom will
/// return None).
pub fn fold_prim<T: Types<Ty = crate::types::Ty> + LiteralTypes>(
    t: &mut T,
    prim: &Prim,
    env: &HashMap<Var, T::Ty>,
    atom_names: &[String],
    nominals: Nominals<'_>,
) -> Option<T::Ty> {
    match prim {
        Prim::Const(c) => fold_const(t, c, atom_names),
        Prim::BinOp(op, a, b) => fold_binop(t, *op, *a, *b, env, nominals),
        Prim::UnOp(op, v) => fold_unop(t, *op, *v, env),
        Prim::MakeTuple(vs) => fold_make_tuple(t, vs, env),
        Prim::MakeStruct { .. } => None,
        Prim::TupleField(v, i) => fold_tuple_field(t, *v, *i as usize, env),
        Prim::StructField(_, _) => None,
        Prim::TypeTest(v, descr) => fold_type_test(t, *v, descr, env),
        // List structural folding requires IR-walking (RED.3+); the type
        // lattice's `list_of(elem)` loses length info. `IsEmptyList` is the
        // exception — type-level subtyping is enough.
        Prim::IsEmptyList(v) => fold_list_is_nil(t, *v, env),
        Prim::IsListCons(v) => fold_list_is_cons(t, *v, env),
        // fz-f88.3 — empty list literal folds to the explicit `[]` type.
        // Non-empty MakeList still loses length info (L1 follow-up fz-4lo).
        Prim::MakeList(elems, tail_v) if elems.is_empty() && tail_v.is_none() => {
            Some(t.empty_list())
        }
        // fz-jg5.6: closure_lit fold — when MakeClosure's captures are
        // all literal, the closure Var has a closure_lit(F, captures) type.
        // The reducer's walk_block uses this to dispatch CallClosure /
        // TailCallClosure to F directly.
        Prim::MakeClosure(_, fn_id, captured) => fold_make_closure(t, *fn_id, captured, env),
        // Other Prims are not foldable via the type lattice in v1.
        Prim::Extern(..)
        | Prim::DestTupleBegin { .. }
        | Prim::DestTupleSet { .. }
        | Prim::DestFreeze { .. }
        | Prim::DestListBegin { .. }
        | Prim::DestListCons { .. }
        | Prim::DestListFreeze { .. }
        | Prim::ListHead(..)
        | Prim::ListTail(..)
        | Prim::MakeList(..)
        | Prim::MakeMap(..)
        | Prim::MapUpdate(..)
        | Prim::DestMapBegin { .. }
        | Prim::DestMapPut { .. }
        | Prim::DestMapFreeze { .. }
        | Prim::MapGet(..)
        | Prim::MatcherMapGet(..)
        | Prim::IsMatcherMapMiss(..)
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
    Some(match c {
        Const::Int(n) => t.int_lit(*n),
        Const::Float(f) => t.float_lit(*f),
        Const::Nil => t.nil(),
        Const::True => t.bool_lit(true),
        Const::False => t.bool_lit(false),
        Const::Atom(id) => {
            let name = atom_names.get(*id as usize)?;
            t.atom_lit(name)
        }
    })
}

fn fold_binop<T: Types<Ty = crate::types::Ty> + LiteralTypes>(
    t: &mut T,
    op: BinOp,
    a: Var,
    b: Var,
    env: &HashMap<Var, T::Ty>,
    nominals: Nominals<'_>,
) -> Option<T::Ty> {
    let ad = env.get(&a)?;
    let bd = env.get(&b)?;
    use BinOp::*;
    match op {
        Add | Sub | Mul | Div | Mod => fold_arith(t, op, ad, bd),
        Eq | Neq => fold_runtime_eq(t, op, ad, bd, nominals).map(|b| t.bool_lit(b)),
        Lt | Le | Gt | Ge => fold_cmp(t, op, ad, bd),
        And | Or => fold_logical(t, op, ad, bd),
    }
}

fn fold_arith<T: Types>(t: &mut T, op: BinOp, ad: &T::Ty, bd: &T::Ty) -> Option<T::Ty> {
    if let (Some(ai), Some(bi)) = (t.as_int_singleton(ad), t.as_int_singleton(bd)) {
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
        return Some(t.int_lit(r));
    }
    if let (Some(af), Some(bf)) = (t.as_float_singleton(ad), t.as_float_singleton(bd)) {
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
        return Some(t.float_lit(r));
    }
    None
}

/// fz-bsx.2 — the reducer's compile-time decision for `==`/`!=`. Returns
/// `Some(true/false)` when the result is statically known, else `None` (emit
/// the runtime comparison). Codegen makes the same decision independently via
/// `descrs_value_disjoint`; both bottom out in the one shared relation,
/// `is_value_disjoint`.
///
/// Runtime equality is brand-BLIND (`ir_brand_erase` strips brands;
/// `fz_value_eq` compares bytes), so the "definitely unequal" arm uses
/// `is_value_disjoint` (brand-erased), NOT `is_disjoint`. The both-literal
/// arm is unchanged: a minted brand is a pure tag, never a singleton, so it
/// never reaches `is_literal`, and `is_equivalent` only sees brand-free
/// literals there.
fn fold_runtime_eq<T: Types<Ty = crate::types::Ty> + LiteralTypes>(
    t: &T,
    op: BinOp,
    ad: &T::Ty,
    bd: &T::Ty,
    nominals: Nominals<'_>,
) -> Option<bool> {
    let is_eq = matches!(op, BinOp::Eq);

    // Both literal: exact compare (brand-free — see doc).
    if t.is_literal(ad) && t.is_literal(bd) {
        return Some(is_eq == t.is_equivalent(ad, bd));
    }

    // Definitely unequal: disjoint in the brand-erased (runtime) model.
    if !t.is_empty(ad) && !t.is_empty(bd) && t.is_value_disjoint(ad, bd, nominals) {
        return Some(!is_eq);
    }

    None
}

fn fold_cmp<T: Types>(t: &mut T, op: BinOp, ad: &T::Ty, bd: &T::Ty) -> Option<T::Ty> {
    use BinOp::*;
    if let (Some(ai), Some(bi)) = (t.as_int_singleton(ad), t.as_int_singleton(bd)) {
        let b = match op {
            Lt => ai < bi,
            Le => ai <= bi,
            Gt => ai > bi,
            Ge => ai >= bi,
            _ => return None,
        };
        return Some(t.bool_lit(b));
    }
    if let (Some(af), Some(bf)) = (t.as_float_singleton(ad), t.as_float_singleton(bd)) {
        let b = match op {
            Lt => af < bf,
            Le => af <= bf,
            Gt => af > bf,
            Ge => af >= bf,
            _ => return None,
        };
        return Some(t.bool_lit(b));
    }
    None
}

fn fold_logical<T: Types + LiteralTypes>(
    t: &mut T,
    op: BinOp,
    ad: &T::Ty,
    bd: &T::Ty,
) -> Option<T::Ty> {
    let ab = t.as_bool_lit(ad)?;
    let bb = t.as_bool_lit(bd)?;
    let r = match op {
        BinOp::And => ab && bb,
        BinOp::Or => ab || bb,
        _ => return None,
    };
    Some(t.bool_lit(r))
}

fn fold_unop<T: Types + LiteralTypes>(
    t: &mut T,
    op: UnOp,
    v: Var,
    env: &HashMap<Var, T::Ty>,
) -> Option<T::Ty> {
    let d = env.get(&v)?;
    match op {
        UnOp::Neg => {
            if let Some(n) = t.as_int_singleton(d) {
                Some(t.int_lit(n.checked_neg()?))
            } else {
                t.as_float_singleton(d).map(|f| t.float_lit(-f))
            }
        }
        UnOp::Not => Some(t.bool_lit(!t.as_bool_lit(d)?)),
    }
}

fn fold_make_tuple<T: Types + LiteralTypes>(
    t: &mut T,
    vs: &[Var],
    env: &HashMap<Var, T::Ty>,
) -> Option<T::Ty> {
    let mut elems: Vec<T::Ty> = Vec::with_capacity(vs.len());
    for v in vs {
        let ty = env.get(v)?;
        if !t.is_literal(ty) {
            return None;
        }
        elems.push(ty.clone());
    }
    Some(t.tuple(&elems))
}

fn fold_tuple_field<T: Types + LiteralTypes>(
    t: &mut T,
    v: Var,
    i: usize,
    env: &HashMap<Var, T::Ty>,
) -> Option<T::Ty> {
    let d = env.get(&v)?;
    let arity = t.max_tuple_arity(d);
    if !t.is_literal(d) || arity <= i {
        return None;
    }
    t.tuple_projections(d, arity).get(i).cloned()
}

fn fold_type_test<T: Types<Ty = crate::types::Ty>>(
    t: &mut T,
    v: Var,
    descr: &crate::types::Ty,
    env: &HashMap<Var, T::Ty>,
) -> Option<T::Ty> {
    let vd = env.get(&v)?;
    if t.is_subtype(vd, descr) {
        Some(t.bool_lit(true))
    } else if t.is_disjoint(vd, descr) {
        Some(t.bool_lit(false))
    } else {
        None
    }
}

/// fz-jg5.6: produce a `closure_lit(F, [literal captures])` type when
/// every captured Var has a literal type in `env`. The reducer then
/// dispatches calls through this closure to `F` directly.
fn fold_make_closure<T: Types + LiteralTypes>(
    t: &mut T,
    fn_id: crate::fz_ir::FnId,
    captured: &[Var],
    env: &HashMap<Var, T::Ty>,
) -> Option<T::Ty> {
    let mut caps: Vec<T::Ty> = Vec::with_capacity(captured.len());
    for cv in captured {
        let ty = env.get(cv)?;
        if !t.is_literal(ty) {
            return None;
        }
        caps.push(ty.clone());
    }
    // n_args is the closure's apparent post-capture arity. We don't
    // know it here without consulting Module.fn_by_id; passing 0 means
    // downstream consumers must look up the body's true arity. The
    // reducer's call-dispatch path consults the body directly, so this
    // 0 placeholder is fine.
    Some(t.closure_lit(fn_id.into(), caps, 0))
}

fn fold_list_is_nil<T: Types>(t: &mut T, v: Var, env: &HashMap<Var, T::Ty>) -> Option<T::Ty> {
    let d = env.get(&v)?;
    // fz-yan.1 — post-fz-s9y, `nil` (the atom) and `[]` (the empty list
    // sentinel) are distinct bit patterns. `IsEmptyList` tests for the
    // EMPTY_LIST sentinel, so a value provably equal to `nil` folds to
    // `false`, not `true` as it did pre-s9y. A value provably equal to
    // `[]` folds to `true`.
    if t.is_nil(d) {
        Some(t.bool_lit(false))
    } else if t.is_empty_list_lit(d) {
        Some(t.bool_lit(true))
    } else {
        None
    }
}

fn fold_list_is_cons<T: Types>(t: &mut T, v: Var, env: &HashMap<Var, T::Ty>) -> Option<T::Ty> {
    let d = env.get(&v)?;
    let any = t.any();
    let cons = t.non_empty_list(any);
    if t.is_subtype(d, &cons) {
        Some(t.bool_lit(true))
    } else {
        let overlap = t.intersect(d.clone(), cons);
        if t.is_empty(&overlap) {
            Some(t.bool_lit(false))
        } else {
            None
        }
    }
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

/// Outcome of dispatching a list of clauses against subject tys.
#[derive(Debug, Clone)]
#[allow(dead_code)] // wired by RED.4+.
pub enum Dispatch<T: Types> {
    /// `row_idx` is the lowest-index row whose patterns and guard match
    /// the subject types (first-match-wins). `bindings` carries the
    /// source-name → literal-Ty map the row's body sees.
    MatchedRow {
        row_idx: usize,
        bindings: HashMap<String, T::Ty>,
    },
    /// Every row has provably-disjoint patterns or a provably-false guard.
    /// Runtime would raise function_clause / match_error. The reducer
    /// should leave the call in place.
    NoMatch,
    /// Cannot statically pick a row. Reducer emits a body for the callee.
    Opaque,
}

/// First-match-wins dispatch of `clauses` against `subject_tys`.
///
/// Algorithm:
/// - For each row in source order, try to match every pattern against the
///   corresponding subject type (`match_pattern`).
/// - If all patterns match and the guard (if any) folds to `true`, return
///   `MatchedRow`.
/// - If any pattern is provably-disjoint, OR a guard folds to `false`,
///   skip the row.
/// - If any pattern OR the guard is indeterminate (Opaque), return Opaque
///   immediately — we cannot prove this row is OR isn't selected; trying
///   later rows would be unsound since this row might match at runtime.
/// - If every row is skipped (NoMatch), return NoMatch.
#[allow(dead_code)] // wired by RED.4+.
pub fn dispatch_clauses<T: Types<Ty = crate::types::Ty> + LiteralTypes>(
    t: &mut T,
    clauses: &[Clause<'_>],
    subject_tys: &[T::Ty],
    atom_names: &[String],
    nominals: Nominals<'_>,
) -> Dispatch<T> {
    for (idx, row) in clauses.iter().enumerate() {
        if row.patterns.len() != subject_tys.len() {
            return Dispatch::Opaque; // arity mismatch is the caller's bug
        }
        let mut bindings: HashMap<String, T::Ty> = HashMap::new();
        let mut all_match = true;
        let mut row_opaque = false;
        for (pat, d) in row.patterns.iter().zip(subject_tys.iter()) {
            match match_pattern(t, &pat.node, d, &mut bindings, atom_names) {
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
            match fold_expr(t, &guard.node, &bindings, atom_names, nominals) {
                Some(d) => match t.as_bool_lit(&d) {
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

/// Match a single AST `Pattern` against a subject ty. On `Match::Yes`,
/// any `Pattern::Var(name)` and `Pattern::As(name, _)` records bind `name`
/// to the (sub-)ty of the subject.
#[allow(dead_code)] // helpers for dispatch_clauses.
fn match_pattern<T: Types + LiteralTypes>(
    t: &mut T,
    pat: &Pattern,
    d: &T::Ty,
    bindings: &mut HashMap<String, T::Ty>,
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
            match_pattern(t, &inner.node, d, bindings, atom_names)
        }
        Int(n) => {
            let expected = t.int_lit(*n);
            match_literal(t, d, &expected)
        }
        Float(f) => {
            let expected = t.float_lit(*f);
            match_literal(t, d, &expected)
        }
        Binary(_) => {
            // Post-fz-axu.11 (L3) lowers Pattern::Binary to a bitstring/brand
            // check at the IR level. The AST evaluator never sees a
            // singleton binary Descr to match against, so defer to the
            // IR-level reducer.
            Match::Opaque
        }
        Atom(name) => {
            let expected = t.atom_lit(name);
            match_literal(t, d, &expected)
        }
        Bool(b) => {
            let expected = t.bool_lit(*b);
            match_literal(t, d, &expected)
        }
        Nil => {
            let expected = t.nil();
            match_literal(t, d, &expected)
        }
        Tuple(elems) => match_tuple_pattern(t, elems, d, bindings, atom_names),
        // List patterns require IR-level reasoning (lists' Descrs lose length
        // information — see RED.1 note). Return Opaque so the reducer keeps
        // the call; RED.3+ may extend this.
        List(_, _) => Match::Opaque,
        // Map and Bitstring patterns: defer to a per-row IR-walking fallback
        // (the matrix's `PerRow` decision) — for the reducer, treat as opaque.
        Map(_) | Struct { .. } | Bitstring(_) => Match::Opaque,
        // fz-5vj — `^name` compares against an outer binding's runtime value.
        // The reducer doesn't see runtime values, so this is always Opaque.
        Pinned(_) => Match::Opaque,
    }
}

/// A pattern that demands a specific literal value. Returns Yes if `d` is
/// equal to `expected` (both are singleton-literal of the same shape), No if
/// they're disjoint, Opaque otherwise.
#[allow(dead_code)]
fn match_literal<T: Types + LiteralTypes>(t: &mut T, d: &T::Ty, expected: &T::Ty) -> Match {
    match t.match_literal_ty(d, expected) {
        crate::types::TypeMatch::Yes => Match::Yes,
        crate::types::TypeMatch::No => Match::No,
        crate::types::TypeMatch::Opaque => Match::Opaque,
    }
}

#[allow(dead_code)]
fn match_tuple_pattern<T: Types + LiteralTypes>(
    t: &mut T,
    elems: &[Spanned<Pattern>],
    d: &T::Ty,
    bindings: &mut HashMap<String, T::Ty>,
    atom_names: &[String],
) -> Match {
    let tuple_arity = t.max_tuple_arity(d);
    if tuple_arity == 0 {
        return if t.is_top(d) {
            Match::Opaque
        } else {
            Match::No
        };
    }
    if tuple_arity != elems.len() {
        let any_elems: Vec<T::Ty> = (0..elems.len()).map(|_| t.any()).collect();
        let tuple_shape = t.tuple(&any_elems);
        return if t.is_subtype(d, &tuple_shape) {
            Match::Opaque
        } else {
            Match::No
        };
    }
    let sig_elems = t.tuple_projections(d, elems.len());
    if sig_elems.len() != elems.len() {
        return Match::Opaque;
    }
    let mut saw_opaque = false;
    for (p, ed) in elems.iter().zip(sig_elems.iter()) {
        match match_pattern(t, &p.node, ed, bindings, atom_names) {
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

/// Fold an AST `Expr` to a literal type under `bindings`. Used for guards.
/// Conservative — handles Var lookup, scalar literals, BinOp, UnOp.
/// Anything else returns None (Opaque guard).
#[allow(dead_code)]
// pub for fz-jg5.3's dispatcher; called by fold_expr; main bin's call graph doesn't reach it yet (RED.3+).
#[allow(clippy::only_used_in_recursion)] // atom_names threaded for API symmetry with siblings; future Expr arms may consult it.
pub fn fold_expr<T: Types<Ty = crate::types::Ty> + LiteralTypes>(
    t: &mut T,
    expr: &ast::Expr,
    bindings: &HashMap<String, T::Ty>,
    atom_names: &[String],
    nominals: Nominals<'_>,
) -> Option<T::Ty> {
    use ast::Expr;
    match expr {
        Expr::Var(name) => bindings.get(name).cloned(),
        Expr::Int(n) => Some(t.int_lit(*n)),
        Expr::Float(f) => Some(t.float_lit(*f)),
        Expr::Binary(_) => {
            // Post-fz-axu.11 (L3) lowers Expr::Binary at the IR level to a
            // bitstring+brand. No singleton type representation remains,
            // so AST-level folding gives up here.
            None
        }
        Expr::Atom(s) => Some(t.atom_lit(s)),
        Expr::Bool(b) => Some(t.bool_lit(*b)),
        Expr::Nil => Some(t.nil()),
        Expr::BinOp(op, a, b) => {
            let ad = fold_expr(t, &a.node, bindings, atom_names, nominals)?;
            let bd = fold_expr(t, &b.node, bindings, atom_names, nominals)?;
            ast_binop_fold(t, *op, &ad, &bd, nominals)
        }
        Expr::UnOp(op, v) => {
            let vd = fold_expr(t, &v.node, bindings, atom_names, nominals)?;
            ast_unop_fold(t, *op, &vd)
        }
        Expr::Ascribe(inner, _) => fold_expr(t, &inner.node, bindings, atom_names, nominals),
        _ => None,
    }
}

#[allow(dead_code)] // used via fold_expr; cf. RED.3+ wiring.
fn ast_binop_fold<T: Types<Ty = crate::types::Ty> + LiteralTypes>(
    t: &mut T,
    op: ast::BinOp,
    ad: &T::Ty,
    bd: &T::Ty,
    nominals: Nominals<'_>,
) -> Option<T::Ty> {
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
        // Pipe and Cons aren't fold-prim-able in the same shape; the
        // Elixir-aligned operators desugar away before folding runs.
        Pipe | Cons | ListConcat | ListSubtract | BinConcat | Range | RangeStep | In | NotIn => {
            return None;
        }
    };
    match ir_op {
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
            fold_arith(t, ir_op, ad, bd)
        }
        // Brand-blind, like every other == site (fz-bsx).
        BinOp::Eq | BinOp::Neq => {
            fold_runtime_eq(t, ir_op, ad, bd, nominals).map(|b| t.bool_lit(b))
        }
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => fold_cmp(t, ir_op, ad, bd),
        BinOp::And | BinOp::Or => fold_logical(t, ir_op, ad, bd),
    }
}

#[allow(dead_code)] // used via fold_expr.
fn ast_unop_fold<T: Types + LiteralTypes>(t: &mut T, op: ast::UnOp, d: &T::Ty) -> Option<T::Ty> {
    use ast::UnOp::*;
    let ir_op = match op {
        Neg => UnOp::Neg,
        Not => UnOp::Not,
    };
    match ir_op {
        UnOp::Neg => {
            if let Some(n) = t.as_int_singleton(d) {
                Some(t.int_lit(n.checked_neg()?))
            } else {
                t.as_float_singleton(d).map(|f| t.float_lit(-f))
            }
        }
        UnOp::Not => t.as_bool_lit(d).map(|b| t.bool_lit(!b)),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::Var;
    use crate::types::ConcreteTypes;

    fn ct() -> ConcreteTypes {
        ConcreteTypes
    }

    fn v(n: u32) -> Var {
        Var(n)
    }

    fn env(pairs: &[(u32, crate::types::Ty)]) -> HashMap<Var, crate::types::Ty> {
        pairs.iter().map(|(i, ty)| (Var(*i), ty.clone())).collect()
    }

    fn tys(ts: &[crate::types::Ty]) -> Vec<crate::types::Ty> {
        ts.to_vec()
    }

    fn assert_int_ty(t: &ConcreteTypes, ty: &crate::types::Ty, n: i64) {
        assert_eq!(t.as_int_singleton(ty), Some(n));
    }

    fn assert_bool_ty(t: &ConcreteTypes, ty: &crate::types::Ty, b: bool) {
        assert_eq!(t.as_bool_lit(ty), Some(b));
    }

    fn assert_atom_ty(t: &ConcreteTypes, ty: &crate::types::Ty, atom: &str) {
        assert_eq!(t.as_atom_singleton(ty).as_deref(), Some(atom));
    }

    fn assert_nil_ty(t: &ConcreteTypes, ty: &crate::types::Ty) {
        assert!(t.is_nil(ty));
    }

    fn assert_num_tuple_ty(t: &ConcreteTypes, ty: &crate::types::Ty, n: i64) {
        let elems = t.tuple_lit_elems(ty).expect("expected literal tuple");
        assert_eq!(elems.len(), 2);
        assert_atom_ty(t, &elems[0], "num");
        assert_int_ty(t, &elems[1], n);
    }

    fn num_tuple_ty(t: &mut ConcreteTypes, n: i64) -> crate::types::Ty {
        let num = t.atom_lit("num");
        let value = t.int_lit(n);
        t.tuple(&[num, value])
    }

    // ---- fold_const ----

    #[test]
    fn fold_const_int() {
        let mut t = ct();
        let r = fold_prim(
            &mut t,
            &Prim::Const(Const::Int(42)),
            &HashMap::new(),
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_int_ty(&t, &r, 42);
    }

    #[test]
    fn fold_const_nil_and_bools() {
        let mut t = ct();
        let nil = fold_prim(
            &mut t,
            &Prim::Const(Const::Nil),
            &HashMap::new(),
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_nil_ty(&t, &nil);
        let bt = fold_prim(
            &mut t,
            &Prim::Const(Const::True),
            &HashMap::new(),
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &bt, true);
        let bf = fold_prim(
            &mut t,
            &Prim::Const(Const::False),
            &HashMap::new(),
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &bf, false);
    }

    #[test]
    fn fold_const_atom_uses_atom_table() {
        let mut t = ct();
        let names = vec!["alpha".to_string(), "beta".to_string()];
        let a = fold_prim(
            &mut t,
            &Prim::Const(Const::Atom(1)),
            &HashMap::new(),
            &names,
            Nominals::empty(),
        )
        .unwrap();
        assert_atom_ty(&t, &a, "beta");
    }

    #[test]
    fn fold_const_atom_out_of_range_returns_none() {
        let names: Vec<String> = vec![];
        assert!(
            fold_prim(
                &mut ct(),
                &Prim::Const(Const::Atom(0)),
                &HashMap::new(),
                &names,
                Nominals::empty()
            )
            .is_none()
        );
    }

    // ---- arithmetic ----

    #[test]
    fn fold_int_add() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(41)), (1, t.int_lit(1))]);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::Add, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_int_ty(&t, &r, 42);
    }

    #[test]
    fn fold_int_div_by_zero_returns_none() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(10)), (1, t.int_lit(0))]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::BinOp(BinOp::Div, v(0), v(1)),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    #[test]
    fn fold_int_overflow_returns_none() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(i64::MAX)), (1, t.int_lit(1))]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::BinOp(BinOp::Add, v(0), v(1)),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    #[test]
    fn fold_float_arith() {
        let mut t = ct();
        let env = env(&[(0, t.float_lit(1.5)), (1, t.float_lit(2.5))]);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::Add, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_eq!(t.as_float_singleton(&r), Some(4.0));
    }

    #[test]
    fn fold_mixed_int_float_returns_none() {
        // No coercion; the planner's policy is no auto-promotion.
        let mut t = ct();
        let env = env(&[(0, t.int_lit(1)), (1, t.float_lit(2.0))]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::BinOp(BinOp::Add, v(0), v(1)),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    #[test]
    fn fold_arith_on_wide_input_returns_none() {
        let mut t = ct();
        let env = env(&[(0, t.int()), (1, t.int_lit(1))]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::BinOp(BinOp::Add, v(0), v(1)),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    // ---- comparison ----

    #[test]
    fn fold_int_lt() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(1)), (1, t.int_lit(2))]);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::Lt, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, true);
    }

    // ---- equality + kind-disjoint fold ----

    #[test]
    fn fold_eq_literal_match() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(42)), (1, t.int_lit(42))]);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::Eq, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, true);
    }

    #[test]
    fn fold_eq_literal_mismatch() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(42)), (1, t.int_lit(7))]);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::Eq, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, false);
    }

    #[test]
    fn fold_neq_literal_mismatch_is_true() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(42)), (1, t.int_lit(7))]);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::Neq, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, true);
    }

    #[test]
    fn fold_eq_kind_disjoint_non_literal() {
        // int vs atom_top: kinds disjoint at the lattice level.
        // VR.5a's case — fold to false even though operands aren't literal.
        let mut t = ct();
        let env = env(&[(0, t.int()), (1, t.atom())]);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::Eq, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, false);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::Neq, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, true);
    }

    #[test]
    fn fold_eq_overlapping_non_literal_returns_none() {
        // int vs int: kinds overlap; cannot decide statically.
        let mut t = ct();
        let env = env(&[(0, t.int()), (1, t.int())]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::BinOp(BinOp::Eq, v(0), v(1)),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    #[test]
    fn fold_runtime_eq_is_brand_blind() {
        // fz-bsx.2: a utf8 (pure brand tag) and an unbranded binary can be
        // byte-equal at runtime, so `==` must NOT fold — even though the
        // brand-aware lattice reports them disjoint. But a utf8 vs an int is
        // genuinely value-disjoint and still folds.
        use crate::concrete_types::{Descr, ty_from_descr};
        let t = ct();
        let utf8 = ty_from_descr(Descr::brand_of("utf8"));
        let binary = ty_from_descr(Descr::str_t());
        let int = ty_from_descr(Descr::int());
        let inners: HashMap<String, crate::types::Ty> =
            [("utf8".to_string(), binary.clone())].into_iter().collect();
        let empty = HashMap::new();
        let nominals = Nominals::new(&inners, &empty);

        assert_eq!(
            fold_runtime_eq(&t, BinOp::Eq, &utf8, &binary, nominals),
            None,
            "brand-only disjoint: must defer to the runtime comparison",
        );
        assert_eq!(
            fold_runtime_eq(&t, BinOp::Eq, &utf8, &int, nominals),
            Some(false),
            "value-disjoint: still folds",
        );
    }

    // ---- logical ----

    #[test]
    fn fold_and_bool_lits() {
        let mut t = ct();
        let env = env(&[(0, t.bool_lit(true)), (1, t.bool_lit(false))]);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::And, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, false);
        let env = env_with_true(&mut t);
        let r = fold_prim(
            &mut t,
            &Prim::BinOp(BinOp::Or, v(0), v(1)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, true);
    }

    fn env_with_true(t: &mut ConcreteTypes) -> HashMap<Var, crate::types::Ty> {
        env(&[(0, t.bool_lit(true)), (1, t.bool_lit(false))])
    }

    // ---- unary ----

    #[test]
    fn fold_neg_int() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(5))]);
        let r = fold_prim(
            &mut t,
            &Prim::UnOp(UnOp::Neg, v(0)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_int_ty(&t, &r, -5);
    }

    #[test]
    fn fold_not_bool() {
        let mut t = ct();
        let env = env(&[(0, t.bool_lit(true))]);
        let r = fold_prim(
            &mut t,
            &Prim::UnOp(UnOp::Not, v(0)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, false);
    }

    // ---- tuple ----

    #[test]
    fn fold_make_tuple_of_literals() {
        let mut t = ct();
        let env = env(&[(0, t.atom_lit("num")), (1, t.int_lit(42))]);
        let r = fold_prim(
            &mut t,
            &Prim::MakeTuple(vec![v(0), v(1)]),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        let elems = t.tuple_lit_elems(&r).unwrap();
        assert_eq!(elems.len(), 2);
        assert_atom_ty(&t, &elems[0], "num");
        assert_int_ty(&t, &elems[1], 42);
    }

    #[test]
    fn fold_make_tuple_with_wide_element_is_none() {
        let mut t = ct();
        let env = env(&[(0, t.atom_lit("num")), (1, t.int())]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::MakeTuple(vec![v(0), v(1)]),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    #[test]
    fn fold_tuple_field_literal() {
        let mut t = ct();
        let tup = num_tuple_ty(&mut t, 42);
        let env = env(&[(0, tup)]);
        let r = fold_prim(
            &mut t,
            &Prim::TupleField(v(0), 1),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_int_ty(&t, &r, 42);
        let r = fold_prim(
            &mut t,
            &Prim::TupleField(v(0), 0),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_atom_ty(&t, &r, "num");
    }

    #[test]
    fn fold_tuple_field_out_of_range() {
        let mut t = ct();
        let tup = num_tuple_ty(&mut t, 42);
        let env = env(&[(0, tup)]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::TupleField(v(0), 7),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    // ---- type test ----

    #[test]
    fn fold_type_test_proves_true() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(42))]);
        let int = t.int();
        let r = fold_prim(
            &mut t,
            &Prim::TypeTest(v(0), Box::new(int)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, true);
    }

    #[test]
    fn fold_type_test_proves_false() {
        let mut t = ct();
        let env = env(&[(0, t.int_lit(42))]);
        let atom = t.atom();
        let r = fold_prim(
            &mut t,
            &Prim::TypeTest(v(0), Box::new(atom)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, false);
    }

    #[test]
    fn fold_type_test_undecidable_returns_none() {
        let mut t = ct();
        let env = env(&[(0, t.any())]);
        let int = t.int();
        assert!(
            fold_prim(
                &mut t,
                &Prim::TypeTest(v(0), Box::new(int)),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    // ---- list_is_nil ----

    #[test]
    fn fold_list_is_nil_on_nil() {
        // fz-yan.1 — post-fz-s9y, `nil` ≠ `[]`. A provably-nil value is
        // NOT the empty-list sentinel, so IsEmptyList folds to `false`.
        let mut t = ct();
        let env = env(&[(0, t.nil())]);
        let r = fold_prim(
            &mut t,
            &Prim::IsEmptyList(v(0)),
            &env,
            &[],
            Nominals::empty(),
        )
        .unwrap();
        assert_bool_ty(&t, &r, false);
    }

    #[test]
    fn fold_list_is_nil_on_list_of_int_is_unknown() {
        // fz-yan.1 — post-fz-s9y, `list_of(int)` includes the empty list,
        // so we can no longer fold to `false`. Leave the test to runtime.
        let mut t = ct();
        let elem = t.int_lit(1);
        let env = env(&[(0, t.list(elem))]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::IsEmptyList(v(0)),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    #[test]
    fn fold_list_is_nil_on_maybe_empty_returns_none() {
        // list_of(int) | nil — could be either.
        let mut t = ct();
        let elem = t.int_lit(1);
        let list = t.list(elem);
        let nil = t.nil();
        let maybe_empty = t.union(list, nil);
        let env = env(&[(0, maybe_empty)]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::IsEmptyList(v(0)),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
    }

    // ---- non-foldable prims explicitly return None ----

    #[test]
    fn fold_extern_returns_none() {
        use crate::fz_ir::ExternId;
        let env = HashMap::new();
        assert!(
            fold_prim(
                &mut ct(),
                &Prim::Extern(ExternId(0), vec![]),
                &env,
                &[],
                Nominals::empty(),
            )
            .is_none()
        );
    }

    #[test]
    fn fold_make_list_returns_none() {
        // Lists are folded by IR-walking in RED.3+, not by fold_prim.
        let mut t = ct();
        let env = env(&[(0, t.int_lit(1)), (1, t.int_lit(2))]);
        assert!(
            fold_prim(
                &mut t,
                &Prim::MakeList(vec![v(0), v(1)], None),
                &env,
                &[],
                Nominals::empty()
            )
            .is_none()
        );
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
        let mut t = ct();
        let patterns = vec![pat(Pattern::Wildcard)];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let subject = tys(&[t.any()]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 0, .. }));
    }

    #[test]
    fn dispatch_var_binds_subject_descr() {
        let mut t = ct();
        let patterns = vec![pat(Pattern::Var("n".to_string()))];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let subject = tys(&[t.int_lit(42)]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        match result {
            Dispatch::MatchedRow {
                row_idx: 0,
                bindings,
            } => {
                assert_int_ty(&t, bindings.get("n").unwrap(), 42);
            }
            other => panic!("expected MatchedRow, got {:?}", other),
        }
    }

    #[test]
    fn dispatch_int_literal_match() {
        let mut t = ct();
        let patterns = vec![pat(Pattern::Int(0))];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let subject = tys(&[t.int_lit(0)]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 0, .. }));
    }

    #[test]
    fn dispatch_int_literal_no_match() {
        let mut t = ct();
        let patterns = vec![pat(Pattern::Int(0))];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let subject = tys(&[t.int_lit(7)]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::NoMatch));
    }

    #[test]
    fn dispatch_int_literal_opaque_against_wide_int() {
        let mut t = ct();
        // Literal pattern against wide int type — indeterminate at compile time.
        let patterns = vec![pat(Pattern::Int(0))];
        let clauses = vec![Clause {
            patterns: &patterns,
            guard: None,
        }];
        let subject = tys(&[t.int()]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::Opaque));
    }

    // ---- multi-clause dispatch (ast_eval-shape) ----

    #[test]
    fn dispatch_ast_eval_num_clause() {
        let mut t = ct();
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

        let subject_tys = tys(&[num_tuple_ty(&mut t, 42)]);
        match dispatch_clauses(&mut t, &clauses, &subject_tys, &[], Nominals::empty()) {
            Dispatch::MatchedRow { row_idx, bindings } => {
                assert_eq!(row_idx, 0);
                assert_int_ty(&t, bindings.get("n").unwrap(), 42);
            }
            other => panic!("expected num-clause match, got {:?}", other),
        }
    }

    #[test]
    fn dispatch_ast_eval_add_clause() {
        let mut t = ct();
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

        let inner_a = num_tuple_ty(&mut t, 2);
        let inner_b = num_tuple_ty(&mut t, 3);
        let add = t.atom_lit("add");
        let subject = t.tuple(&[add, inner_a.clone(), inner_b.clone()]);
        let subject_tys = tys(&[subject]);
        match dispatch_clauses(&mut t, &clauses, &subject_tys, &[], Nominals::empty()) {
            Dispatch::MatchedRow { row_idx, bindings } => {
                assert_eq!(row_idx, 1);
                assert_num_tuple_ty(&t, bindings.get("a").unwrap(), 2);
                assert_num_tuple_ty(&t, bindings.get("b").unwrap(), 3);
            }
            other => panic!("expected add-clause match, got {:?}", other),
        }
    }

    #[test]
    fn dispatch_ast_eval_opaque_on_any() {
        let mut t = ct();
        let num_pat = pat(Pattern::Tuple(vec![
            pat(Pattern::Atom("num".to_string())),
            pat(Pattern::Var("n".to_string())),
        ]));
        let c0 = vec![num_pat];
        let clauses = vec![Clause {
            patterns: &c0,
            guard: None,
        }];
        let subject = tys(&[t.any()]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::Opaque));
    }

    // ---- first-match-wins (wildcard_then_specific) ----

    #[test]
    fn dispatch_first_match_wins_over_specific() {
        let mut t = ct();
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
        let subject = tys(&[t.int_lit(0)]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 0, .. }));
    }

    // ---- guard handling (multi_clause-shape) ----

    #[test]
    fn dispatch_guard_true_selects_clause() {
        let mut t = ct();
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
        let subject = tys(&[t.int_lit(7)]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 0, .. }));
    }

    #[test]
    fn dispatch_guard_false_skips_clause() {
        let mut t = ct();
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
        let subject = tys(&[t.int_lit(-3)]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::MatchedRow { row_idx: 1, .. }));
    }

    #[test]
    fn dispatch_guard_indeterminate_returns_opaque() {
        let mut t = ct();
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
        let subject = tys(&[t.int()]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::Opaque));
    }

    // ---- list patterns are opaque in v1 ----

    #[test]
    fn dispatch_list_pattern_opaque() {
        let mut t = ct();
        let pat_list = vec![pat(Pattern::List(vec![pat(Pattern::Wildcard)], None))];
        let clauses = vec![Clause {
            patterns: &pat_list,
            guard: None,
        }];
        let elem = t.int_lit(1);
        let subject = tys(&[t.list(elem)]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::Opaque));
    }

    // ---- As-patterns ----

    #[test]
    fn dispatch_as_pattern_binds_outer_and_matches_inner() {
        let mut t = ct();
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
        let subject_tys = tys(&[num_tuple_ty(&mut t, 42)]);
        match dispatch_clauses(&mut t, &clauses, &subject_tys, &[], Nominals::empty()) {
            Dispatch::MatchedRow { bindings, .. } => {
                assert_num_tuple_ty(&t, bindings.get("whole").unwrap(), 42);
                assert_int_ty(&t, bindings.get("n").unwrap(), 42);
            }
            other => panic!("expected match, got {:?}", other),
        }
    }

    // ---- no-match across multiple clauses ----

    #[test]
    fn dispatch_no_match_when_every_clause_disjoint() {
        let mut t = ct();
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
        let subject = tys(&[t.int_lit(7)]);
        let result = dispatch_clauses(&mut t, &clauses, &subject, &[], Nominals::empty());
        assert!(matches!(result, Dispatch::NoMatch));
    }
}
