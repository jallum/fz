// Public API is consumed by fz-ul4.43.D's lowerer; nothing wires it up
// yet in this commit (.43.C ships data + algorithm only).
#![allow(dead_code)]
//! fz-ul4.43.C — Pattern matrix data types + decision-tree compiler.
//!
//! Compiles a list of clause patterns into a shared decision tree, so that
//! cross-clause constructor tests (same arity, same atom) are emitted ONCE
//! and dispatched into per-clause continuations. Replaces the per-clause
//! `lower_pattern_bind` cascade currently duplicated across
//! `lower_multi_clause`, `lower_case`, and `lower_with`.
//!
//! Algorithm: Maranget-lite. First column with a constructor pattern drives
//! specialization. Wildcards/Vars participate in every specialization
//! (their bindings are recorded). Patterns we don't constructor-specialize
//! (Map, Bitstring) drop a row into `PerRow` fallback — the lowerer handles
//! those sequentially.
//!
//! Scope: ticket .43.C ships types + compile. Wiring into call sites is
//! .43.D (lower_multi_clause), .43.F (lower_case), .43.G (lower_with).

use crate::ast::{Expr, Pattern, Spanned};
use crate::fz_ir::Var;

/// Opaque handle into the caller's body table. The matrix never lowers
/// bodies; it routes Leaves to the caller's body-lowering callback by id.
pub type BodyId = u32;

#[derive(Debug, Clone)]
pub struct Row {
    /// Column patterns. `patterns.len()` must equal `Matrix::subjects.len()`
    /// at every step of compilation. Specialization may grow or shrink this
    /// vector (e.g. tuple-arity-3 specialization replaces one column with three).
    pub patterns: Vec<Spanned<Pattern>>,
    /// `@spec` annotation tests evaluated at leaf-resolution time, before
    /// the guard. Each (var, descr) emits `TypeTest(var, descr)`; on fail,
    /// the matrix falls through to the next row.
    pub preconditions: Vec<(Var, crate::types::Ty)>,
    pub guard: Option<Spanned<Expr>>,
    pub body_id: BodyId,
}

#[derive(Debug, Clone)]
pub struct Matrix {
    pub subjects: Vec<Var>,
    pub rows: Vec<Row>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubjectRef {
    Var(Var),
    TupleField {
        tuple: Box<SubjectRef>,
        index: u32,
    },
}

impl SubjectRef {
    fn root_var(&self) -> Option<Var> {
        match self {
            SubjectRef::Var(v) => Some(*v),
            SubjectRef::TupleField { tuple, .. } => tuple.root_var(),
        }
    }
}

#[derive(Debug, Clone)]
struct CompileMatrix {
    subjects: Vec<SubjectRef>,
    rows: Vec<Row>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubjectDomain {
    Any,
    List,
}

/// What kind of constructor a Switch dispatches on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwitchKind {
    /// Tuple-of-arity-N. Cases keyed on N (u32).
    TupleArity,
    /// Atom literal. Cases keyed on the atom name (interned later by lowerer).
    Atom,
    /// Integer literal.
    Int,
    /// Float literal, keyed by raw IEEE-754 bits.
    Float,
    /// Boolean literal — :true / :false.
    Bool,
    /// Nil literal — only ever has one case (:nil) and a default.
    Nil,
    /// Binary-family literal. UTF-8 values are branded binaries, not a
    /// separate top-level value family.
    Binary,
    /// List shape — cons vs. empty. Cases: IsNil (true) / IsCons (false).
    ListCons,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SwitchKey {
    Arity(u32),
    AtomName(String),
    Int(i64),
    FloatBits(u64),
    Bool(bool),
    /// The `nil` atom-like value. Distinct from `EmptyList` — fz-s9y
    /// splits the runtime representations; the matrix tracks them as
    /// separate constructors so `Pattern::Nil` and `Pattern::List([],None)`
    /// don't silently collapse.
    Nil,
    /// Concrete byte sequence with the UTF-8 brand/refinement.
    Utf8Binary(Vec<u8>),
    /// The empty list value (`[]` literal). After fz-s9y.2 it has a
    /// distinct runtime bit pattern from `Nil`; the matrix already
    /// treats it as a distinct constructor so the bug class can't recur.
    EmptyList,
    Cons,
}

/// A compiled decision tree.
#[derive(Debug, Clone)]
pub enum Decision {
    /// No row matches. Lowerer emits jump to the function-clause fail block.
    Fail,
    /// Successful match — execute the body, possibly after a guard.
    Leaf {
        body_id: BodyId,
        /// (source name, Var-it-resolved-to) bindings the body sees.
        bindings: Vec<(String, SubjectRef)>,
        /// Runtime type preconditions from annotated function heads.
        /// These must be tested before the guard; failure falls through to
        /// `on_guard_fail`, matching `lower_pattern_matrix`'s body callback.
        preconditions: Vec<(Var, crate::types::Ty)>,
        /// If present, eval the guard; on truthy, run body; on falsy, fall
        /// through to `on_guard_fail`.
        guard: Option<Spanned<Expr>>,
        /// Where to go if the guard rejects. None when there's no guard.
        on_guard_fail: Option<Box<Decision>>,
    },
    /// Constructor switch — one shared test, branches into specialized
    /// sub-decisions. The `default` branch covers rows whose pattern was
    /// a wildcard (or whose constructor matched none of the cases).
    Switch {
        subject: SubjectRef,
        kind: SwitchKind,
        cases: Vec<(SwitchKey, Decision)>,
        default: Box<Decision>,
    },
    /// Fallback for patterns the matrix can't constructor-specialize
    /// (Map, Bitstring). Lowerer drops into per-row sequential lowering
    /// against `subject` using the row's first-column pattern; failure
    /// continues to `on_fail`.
    PerRow {
        subject: SubjectRef,
        row: Row,
        on_fail: Box<Decision>,
    },
}

// ---------------------------------------------------------------------------
// Compilation
// ---------------------------------------------------------------------------

/// Compile a matrix into a decision tree.
pub fn compile(m: Matrix) -> Decision {
    compile_inner(CompileMatrix {
        subjects: m.subjects.into_iter().map(SubjectRef::Var).collect(),
        rows: m.rows,
    })
}

fn compile_inner(m: CompileMatrix) -> Decision {
    // No rows → no match possible.
    if m.rows.is_empty() {
        return Decision::Fail;
    }
    // No more columns to test → the first row matches (its bindings have
    // been recorded as patterns were stripped down to wildcards/vars).
    if m.subjects.is_empty() {
        return leaf_or_rejecting_chain(m.rows, vec![]);
    }

    // Pick a column that has at least one constructor in some row. If
    // every column is all-wildcard for every row, the first row matches.
    let col = match pick_specialization_column(&m) {
        Some(c) => c,
        None => return leaf_or_rejecting_chain(m.rows, m.subjects),
    };

    // If any row's chosen column is a Map or Bitstring (or other
    // un-specializable shape), drop into PerRow for that row.
    if let Some(row_idx) = find_unspecializable_row(&m, col) {
        let mut rows = m.rows;
        let row = rows.remove(row_idx);
        let subject = m.subjects[col].clone();
        let rest = CompileMatrix {
            subjects: m.subjects,
            rows,
        };
        return Decision::PerRow {
            subject,
            row,
            on_fail: Box::new(compile_inner(rest)),
        };
    }

    // Specialize the matrix on the chosen column.
    specialize_and_compile(m, col)
}

/// Strip As-patterns into bindings; return the inner pattern.
/// (Var bindings are also returned via `into_bindings`.)
fn peel_as(pat: &Spanned<Pattern>, subject: Var, out: &mut Vec<(String, Var)>) -> Spanned<Pattern> {
    let mut cur = pat.clone();
    loop {
        match &cur.node {
            Pattern::As(name, inner) => {
                out.push((name.clone(), subject));
                let inner_box = inner.clone();
                cur = (*inner_box).clone();
            }
            _ => return cur,
        }
    }
}

fn is_wildlike(p: &Pattern) -> bool {
    matches!(p, Pattern::Wildcard | Pattern::Var(_))
        || matches!(p, Pattern::As(_, inner) if is_wildlike(&inner.node))
}

fn pick_specialization_column(m: &CompileMatrix) -> Option<usize> {
    // Leftmost column that has any non-wildlike pattern across rows.
    (0..m.subjects.len()).find(|&col| m.rows.iter().any(|r| !is_wildlike(&r.patterns[col].node)))
}

fn find_unspecializable_row(m: &CompileMatrix, col: usize) -> Option<usize> {
    for (i, r) in m.rows.iter().enumerate() {
        // Look through As-patterns.
        let mut p = &r.patterns[col].node;
        while let Pattern::As(_, inner) = p {
            p = &inner.node;
        }
        if matches!(p, Pattern::Map(_) | Pattern::Bitstring(_)) {
            return Some(i);
        }
    }
    None
}

fn leaf_or_rejecting_chain(mut rows: Vec<Row>, subjects: Vec<SubjectRef>) -> Decision {
    let row = rows.remove(0);
    let reject = if row_can_reject(&row) {
        Some(Box::new(compile_inner(CompileMatrix { subjects: subjects.clone(), rows })))
    } else {
        None
    };
    leaf_from_row(row, &subjects, reject)
}

fn row_can_reject(row: &Row) -> bool {
    row.guard.is_some() || !row.preconditions.is_empty()
}

fn leaf_from_row(
    row: Row,
    _subjects: &[SubjectRef],
    on_guard_fail: Option<Box<Decision>>,
) -> Decision {
    // `subjects` is unused here because by the time we reach this leaf,
    // either subjects.is_empty() OR every remaining column is wildcard
    // (so no extra binding to do beyond what specialize already recorded).
    // But we still need to extract Var-bindings from wildcard columns
    // when subjects is non-empty.
    let bindings = collect_var_bindings(&row.patterns, _subjects);
    let preconditions = row.preconditions.clone();
    let guard = row.guard.clone();
    Decision::Leaf {
        body_id: row.body_id,
        bindings,
        preconditions,
        guard,
        on_guard_fail,
    }
}

fn collect_var_bindings(
    patterns: &[Spanned<Pattern>],
    subjects: &[SubjectRef],
) -> Vec<(String, SubjectRef)> {
    let mut out = Vec::new();
    for (p, subj) in patterns.iter().zip(subjects.iter()) {
        collect_one(&p.node, &subj, &mut out);
    }
    out
}

fn collect_one(p: &Pattern, subj: &SubjectRef, out: &mut Vec<(String, SubjectRef)>) {
    match p {
        Pattern::Var(name) => out.push((name.clone(), subj.clone())),
        Pattern::As(name, inner) => {
            out.push((name.clone(), subj.clone()));
            collect_one(&inner.node, subj, out);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Specialization
// ---------------------------------------------------------------------------

fn specialize_and_compile(m: CompileMatrix, col: usize) -> Decision {
    let subject = m.subjects[col].clone();
    let kind = pick_kind_for_column(&m, col);
    match kind {
        SwitchKind::TupleArity => specialize_tuple_arity(m, col, subject),
        SwitchKind::Atom => specialize_atom(m, col, subject),
        SwitchKind::Int => specialize_int(m, col, subject),
        SwitchKind::Float => specialize_float(m, col, subject),
        SwitchKind::Bool => specialize_bool(m, col, subject),
        SwitchKind::Nil => specialize_nil(m, col, subject),
        SwitchKind::Binary => specialize_binary(m, col, subject),
        SwitchKind::ListCons => specialize_listcons(m, col, subject),
    }
}

fn pick_kind_for_column(m: &CompileMatrix, col: usize) -> SwitchKind {
    // Use the first row's non-wildlike pattern in this column.
    for r in &m.rows {
        let mut p = &r.patterns[col].node;
        while let Pattern::As(_, inner) = p {
            p = &inner.node;
        }
        match p {
            Pattern::Tuple(_) => return SwitchKind::TupleArity,
            Pattern::Atom(_) => return SwitchKind::Atom,
            Pattern::Int(_) => return SwitchKind::Int,
            Pattern::Float(_) => return SwitchKind::Float,
            Pattern::Bool(_) => return SwitchKind::Bool,
            Pattern::Nil => return SwitchKind::Nil,
            Pattern::Binary(_) => return SwitchKind::Binary,
            Pattern::List(_, _) => return SwitchKind::ListCons,
            _ => continue,
        }
    }
    // Should never reach: pick_specialization_column returned this col
    // because some row was non-wildlike. Fall back conservatively.
    SwitchKind::TupleArity
}

fn specialize_tuple_arity(m: CompileMatrix, col: usize, subject: SubjectRef) -> Decision {
    use std::collections::BTreeMap;
    let mut by_arity: BTreeMap<u32, Vec<Row>> = BTreeMap::new();
    let mut default_rows: Vec<Row> = Vec::new();

    for row in m.rows {
        let mut row = row;
        let (had_binding, inner_pat) = peel_to_inner_with_bind(&row.patterns[col]);
        // had_binding is folded by adding a Var-marker to the row's pattern
        // for the same subject; but since we drop the column on
        // specialization, we instead bake bindings into a synthetic wildcard
        // row pattern carrying them. Simplest: keep the As-binding on the
        // row by leaving it in patterns[col]; the leaf-collector will pick
        // it up. We rewrite the col in-place to the inner pattern.
        row.patterns[col] = inner_pat;
        let _ = had_binding;

        let p = &row.patterns[col].node;
        match p {
            Pattern::Tuple(fields) => {
                let arity = fields.len() as u32;
                let mut new_row = row.clone();
                // Replace col with the tuple's fields (in-place column expansion).
                let span = new_row.patterns[col].span;
                new_row.patterns.splice(col..=col, fields.iter().cloned());
                // Record subject as bound iff wildcard wrapper is present —
                // handled by leaf via Var/As patterns inside fields.
                let _ = span;
                by_arity.entry(arity).or_default().push(new_row);
            }
            Pattern::Wildcard | Pattern::Var(_) => default_rows.push(row),
            _ => {
                // Different constructor in same column → row simply doesn't
                // match any of our arities. Skip.
            }
        }
    }

    // Build per-arity sub-matrices.
    let mut cases: Vec<(SwitchKey, Decision)> = Vec::new();
    for (arity, rows) in by_arity {
        // Subjects: replace `col` with `arity` placeholder subjects. The
        // matrix doesn't actually allocate Vars (that's a lowerer concern);
        // we use a sentinel Var(u32::MAX - i) to mean "field i of subject
        // at index col, to be projected at lowering time." Lowerer
        // recognizes these and rewrites them. See pattern_matrix tests for
        // assertion examples.
        //
        // Simpler approach: subjects stays the same length; we treat the
        // expanded columns as "virtual" by recording the binding intent and
        // let the lowerer project. For .C the data type alone needs to
        // EXPRESS the structure correctly — concrete Var assignment is
        // .D's job.
        //
        // Practical implementation: include default rows (wildcards) that
        // fan out across the new columns as wildcards too.
        let mut all_rows = rows;
        for d in &default_rows {
            let mut dr = d.clone();
            let span = dr.patterns[col].span;
            let wilds: Vec<Spanned<Pattern>> = (0..arity)
                .map(|_| Spanned::new(Pattern::Wildcard, span))
                .collect();
            dr.patterns.splice(col..=col, wilds);
            all_rows.push(dr);
        }
        // fz-ul4.45 — first-match-wins source order preservation.
        all_rows.sort_by_key(|r| r.body_id);
        let mut new_subjects = m.subjects.clone();
        let projections: Vec<SubjectRef> = (0..arity)
            .map(|i| SubjectRef::TupleField {
                tuple: Box::new(subject.clone()),
                index: i,
            })
            .collect();
        new_subjects.splice(col..=col, projections);

        let sub_matrix = CompileMatrix {
            subjects: new_subjects,
            rows: all_rows,
        };
        cases.push((SwitchKey::Arity(arity), compile_inner(sub_matrix)));
    }

    // Default: rows that had wildcard in this column. The subject is dropped.
    let default = {
        let mut new_subjects = m.subjects.clone();
        new_subjects.remove(col);
        let new_rows: Vec<Row> = default_rows
            .into_iter()
            .map(|mut r| {
                r.patterns.remove(col);
                r
            })
            .collect();
        Box::new(compile_inner(CompileMatrix {
            subjects: new_subjects,
            rows: new_rows,
        }))
    };

    Decision::Switch {
        subject,
        kind: SwitchKind::TupleArity,
        cases,
        default,
    }
}

fn specialize_atom(m: CompileMatrix, col: usize, subject: SubjectRef) -> Decision {
    specialize_literal(m, col, subject, SwitchKind::Atom, |p| match p {
        Pattern::Atom(s) => Some(SwitchKey::AtomName(s.clone())),
        _ => None,
    })
}

fn specialize_int(m: CompileMatrix, col: usize, subject: SubjectRef) -> Decision {
    specialize_literal(m, col, subject, SwitchKind::Int, |p| match p {
        Pattern::Int(n) => Some(SwitchKey::Int(*n)),
        _ => None,
    })
}

fn specialize_float(m: CompileMatrix, col: usize, subject: SubjectRef) -> Decision {
    specialize_literal(m, col, subject, SwitchKind::Float, |p| match p {
        Pattern::Float(n) => Some(SwitchKey::FloatBits(n.to_bits())),
        _ => None,
    })
}

fn specialize_bool(m: CompileMatrix, col: usize, subject: SubjectRef) -> Decision {
    specialize_literal(m, col, subject, SwitchKind::Bool, |p| match p {
        Pattern::Bool(b) => Some(SwitchKey::Bool(*b)),
        _ => None,
    })
}

fn specialize_nil(m: CompileMatrix, col: usize, subject: SubjectRef) -> Decision {
    specialize_literal(m, col, subject, SwitchKind::Nil, |p| match p {
        Pattern::Nil => Some(SwitchKey::Nil),
        _ => None,
    })
}

fn specialize_binary(m: CompileMatrix, col: usize, subject: SubjectRef) -> Decision {
    specialize_literal(m, col, subject, SwitchKind::Binary, |p| match p {
        Pattern::Binary(bytes) => Some(SwitchKey::Utf8Binary(bytes.clone())),
        _ => None,
    })
}

fn specialize_listcons(m: CompileMatrix, col: usize, subject: SubjectRef) -> Decision {
    // List patterns: [] is Nil, [h|t] is Cons. Specialize on Cons drops a
    // single column (the cons head/tail are inside the pattern, not the
    // matrix subjects — head/tail projection happens at lowering time
    // via Prim::ListHead/Tail, then PerRow can take over for the inner
    // bindings, since List patterns nested arbitrarily are uncommon
    // enough to keep PerRow here for .C/.D scope).
    use std::collections::BTreeMap;
    let mut by_key: BTreeMap<SwitchKey, Vec<Row>> = BTreeMap::new();
    let mut default_rows: Vec<Row> = Vec::new();

    for row in m.rows {
        let mut row = row;
        let (_, inner_pat) = peel_to_inner_with_bind(&row.patterns[col]);
        row.patterns[col] = inner_pat;
        let p = &row.patterns[col].node;
        match p {
            Pattern::Nil => {
                let mut r = row.clone();
                r.patterns.remove(col);
                by_key.entry(SwitchKey::Nil).or_default().push(r);
            }
            Pattern::List(elems, tail) => {
                if elems.is_empty() && tail.is_none() {
                    // `[]` literal — distinct from `nil` after fz-s9y.2's
                    // runtime split. Pre-fz-s9y.1 this was a `continue`
                    // that silently dropped the row, surfacing as bogus
                    // "unreachable arm" + "inexhaustive" diagnostics on
                    // every nil/cons fn definition. Route to its own
                    // SwitchKey so the decision tree is well-formed.
                    let mut r = row.clone();
                    r.patterns.remove(col);
                    by_key.entry(SwitchKey::EmptyList).or_default().push(r);
                } else if elems.is_empty() {
                    // `[| tail]` form — parser disallows (must parse ≥1
                    // pattern before `|`); kept here as a defensive
                    // unreachable branch.
                    continue;
                } else {
                    // Cons-form: keep the row but drop column (PerRow
                    // handles the inner head/tail bindings).
                    by_key.entry(SwitchKey::Cons).or_default().push(row);
                }
            }
            Pattern::Wildcard | Pattern::Var(_) => default_rows.push(row),
            _ => {}
        }
    }

    let mut cases: Vec<(SwitchKey, Decision)> = Vec::new();
    for (key, mut rows) in by_key {
        for d in &default_rows {
            rows.push(d.clone());
        }
        rows.sort_by_key(|r| r.body_id);
        // Nil / EmptyList sub-decisions: the pattern matched a leaf value,
        // no head/tail to project — column already removed above. Cons
        // sub-decisions: drop the column here so PerRow can project
        // head/tail.
        let column_already_removed = matches!(key, SwitchKey::Nil | SwitchKey::EmptyList);
        let new_subjects = if column_already_removed {
            let mut s = m.subjects.clone();
            s.remove(col);
            s
        } else {
            m.subjects.clone()
        };
        let rows = if column_already_removed {
            rows
        } else {
            // Drop column for cons-rows too: per-row will project.
            rows.into_iter()
                .map(|mut r| {
                    r.patterns.remove(col);
                    r
                })
                .collect()
        };
        let sub_subjects = if !column_already_removed {
            let mut s = m.subjects.clone();
            s.remove(col);
            s
        } else {
            new_subjects
        };
        cases.push((
            key,
            compile_inner(CompileMatrix {
                subjects: sub_subjects,
                rows,
            }),
        ));
    }

    let default = {
        let mut new_subjects = m.subjects.clone();
        new_subjects.remove(col);
        let new_rows: Vec<Row> = default_rows
            .into_iter()
            .map(|mut r| {
                r.patterns.remove(col);
                r
            })
            .collect();
        Box::new(compile_inner(CompileMatrix {
            subjects: new_subjects,
            rows: new_rows,
        }))
    };

    Decision::Switch {
        subject,
        kind: SwitchKind::ListCons,
        cases,
        default,
    }
}

fn specialize_literal<F>(
    m: CompileMatrix,
    col: usize,
    subject: SubjectRef,
    kind: SwitchKind,
    key_for: F,
) -> Decision
where
    F: Fn(&Pattern) -> Option<SwitchKey>,
{
    use std::collections::BTreeMap;
    let mut by_key: BTreeMap<String, (SwitchKey, Vec<Row>)> = BTreeMap::new();
    let mut default_rows: Vec<Row> = Vec::new();

    for row in m.rows {
        let mut row = row;
        let (_, inner_pat) = peel_to_inner_with_bind(&row.patterns[col]);
        row.patterns[col] = inner_pat;
        let p = &row.patterns[col].node;
        if let Some(k) = key_for(p) {
            let kstr = format!("{:?}", k); // for BTreeMap ordering; not stored
            let mut nr = row.clone();
            nr.patterns.remove(col);
            by_key
                .entry(kstr)
                .or_insert_with(|| (k, Vec::new()))
                .1
                .push(nr);
        } else if matches!(p, Pattern::Wildcard | Pattern::Var(_)) {
            default_rows.push(row);
        }
    }

    let mut cases: Vec<(SwitchKey, Decision)> = Vec::new();
    for (_, (key, mut rows)) in by_key {
        for d in &default_rows {
            let mut dr = d.clone();
            dr.patterns.remove(col);
            rows.push(dr);
        }
        rows.sort_by_key(|r| r.body_id);
        let mut new_subjects = m.subjects.clone();
        new_subjects.remove(col);
        cases.push((
            key,
            compile_inner(CompileMatrix {
                subjects: new_subjects,
                rows,
            }),
        ));
    }

    let default = {
        let mut new_subjects = m.subjects.clone();
        new_subjects.remove(col);
        let new_rows: Vec<Row> = default_rows
            .into_iter()
            .map(|mut r| {
                r.patterns.remove(col);
                r
            })
            .collect();
        Box::new(compile_inner(CompileMatrix {
            subjects: new_subjects,
            rows: new_rows,
        }))
    };

    Decision::Switch {
        subject,
        kind,
        cases,
        default,
    }
}

/// Strip As-bindings off a column pattern, recording each As-name as
/// a binding to `subject`. Returns (had_at_least_one_binding, inner_pat).
fn peel_to_inner_with_bind(pat: &Spanned<Pattern>) -> (bool, Spanned<Pattern>) {
    let mut had = false;
    let mut cur = pat.clone();
    while let Pattern::As(_, inner) = &cur.node {
        had = true;
        let inner_box = inner.clone();
        cur = (*inner_box).clone();
    }
    (had, cur)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// fz-ul4.45 — Exhaustiveness + unreachability analysis
// ---------------------------------------------------------------------------

/// Body ids that no path through the decision tree reaches. A row whose
/// body_id is in this set is unreachable — earlier rows fully cover its
/// matching space, OR its pattern conflicts with an earlier specialization.
///
/// fz-rcp.2 — guarded rows do NOT consume coverage. A guard is a runtime
/// predicate that can reject, so a row whose guard fails falls through
/// to the next row. For each row R we ask: "is R's pattern unreachable
/// given only the preceding unguarded rows?" — i.e., we form a sub-matrix
/// containing the unguarded prefix ending with R and check whether R's
/// body_id is reached there. R's own guard doesn't affect the check
/// (we're testing pattern coverage, not whether R itself matches at
/// runtime).
pub fn find_unreachable_rows(matrix: &Matrix) -> Vec<BodyId> {
    // Fast path: no guards anywhere → original single-compile behavior.
    if matrix.rows.iter().all(|r| r.guard.is_none()) {
        let row_bodies: std::collections::BTreeSet<BodyId> =
            matrix.rows.iter().map(|r| r.body_id).collect();
        let decision = compile(matrix.clone());
        let mut reached = std::collections::BTreeSet::new();
        collect_reachable_bodies(&decision, &mut reached);
        return row_bodies.difference(&reached).copied().collect();
    }
    // Guarded matrix: walk row-by-row, accumulating only unguarded rows
    // into the prefix used to test subsequent rows.
    let mut unreachable: Vec<BodyId> = Vec::new();
    let mut unguarded_prefix: Vec<Row> = Vec::new();
    for row in &matrix.rows {
        let mut test_rows = unguarded_prefix.clone();
        test_rows.push(row.clone());
        let test_matrix = Matrix {
            subjects: matrix.subjects.clone(),
            rows: test_rows,
        };
        let decision = compile(test_matrix);
        let mut reached = std::collections::BTreeSet::new();
        collect_reachable_bodies(&decision, &mut reached);
        if !reached.contains(&row.body_id) {
            unreachable.push(row.body_id);
        }
        if row.guard.is_none() {
            unguarded_prefix.push(row.clone());
        }
    }
    unreachable
}

/// True if any path through the decision tree leads to Fail — i.e., the
/// matrix doesn't cover all possible subject values. Lowerers like
/// lower_case translate this to a runtime `:case_clause` halt; the warning
/// surfaces the gap at compile time.
pub fn is_inexhaustive(matrix: &Matrix) -> bool {
    is_inexhaustive_with_domains(matrix, &[])
}

pub fn is_inexhaustive_with_domains(matrix: &Matrix, domains: &[SubjectDomain]) -> bool {
    let decision = compile(matrix.clone());
    let domain_by_subject: std::collections::HashMap<Var, SubjectDomain> = matrix
        .subjects
        .iter()
        .copied()
        .zip(domains.iter().copied())
        .collect();
    has_reachable_fail(&decision, &domain_by_subject)
}

fn collect_reachable_bodies(d: &Decision, out: &mut std::collections::BTreeSet<BodyId>) {
    match d {
        Decision::Fail => {}
        Decision::Leaf {
            body_id,
            on_guard_fail,
            ..
        } => {
            out.insert(*body_id);
            if let Some(reject) = on_guard_fail {
                collect_reachable_bodies(reject, out);
            }
        }
        Decision::Switch { cases, default, .. } => {
            for (_, sub) in cases {
                collect_reachable_bodies(sub, out);
            }
            collect_reachable_bodies(default, out);
        }
        Decision::PerRow { row, on_fail, .. } => {
            out.insert(row.body_id);
            collect_reachable_bodies(on_fail, out);
        }
    }
}

fn has_reachable_fail(
    d: &Decision,
    domain_by_subject: &std::collections::HashMap<Var, SubjectDomain>,
) -> bool {
    match d {
        Decision::Fail => true,
        Decision::Leaf { on_guard_fail, .. } => on_guard_fail
            .as_deref()
            .is_some_and(|reject| has_reachable_fail(reject, domain_by_subject)),
        Decision::Switch { cases, default, .. } => {
            if cases
                .iter()
                .any(|(_, sub)| has_reachable_fail(sub, domain_by_subject))
            {
                return true;
            }
            if list_domain_is_covered(d, domain_by_subject) {
                return false;
            }
            has_reachable_fail(default, domain_by_subject)
        }
        Decision::PerRow { on_fail, .. } => has_reachable_fail(on_fail, domain_by_subject),
    }
}

fn list_domain_is_covered(
    d: &Decision,
    domain_by_subject: &std::collections::HashMap<Var, SubjectDomain>,
) -> bool {
    let Decision::Switch {
        subject,
        kind: SwitchKind::ListCons,
        cases,
        ..
    } = d
    else {
        return false;
    };
    if subject
        .root_var()
        .and_then(|v| domain_by_subject.get(&v).copied())
        != Some(SubjectDomain::List)
    {
        return false;
    }
    let has_empty = cases
        .iter()
        .any(|(key, _)| matches!(key, SwitchKey::EmptyList));
    let has_cons = cases.iter().any(|(key, _)| matches!(key, SwitchKey::Cons));
    has_empty && has_cons
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Pattern, Spanned};
    use crate::diag::FileId;

    fn sp<T>(node: T) -> Spanned<T> {
        let _ = FileId(0);
        Spanned::dummy(node)
    }

    fn row(patterns: Vec<Pattern>, body_id: BodyId) -> Row {
        Row {
            patterns: patterns.into_iter().map(sp).collect(),
            preconditions: Vec::new(),
            guard: None,
            body_id,
        }
    }

    #[test]
    fn empty_matrix_compiles_to_fail() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![],
        };
        match compile(m) {
            Decision::Fail => {}
            other => panic!("expected Fail, got {:?}", other),
        }
    }

    #[test]
    fn all_wildcard_rows_compile_to_first_row_leaf() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Wildcard], 7),
                row(vec![Pattern::Wildcard], 8),
            ],
        };
        match compile(m) {
            Decision::Leaf { body_id: 7, .. } => {}
            other => panic!("expected Leaf body_id=7, got {:?}", other),
        }
    }

    #[test]
    fn var_pattern_records_binding_in_leaf() {
        let m = Matrix {
            subjects: vec![Var(42)],
            rows: vec![row(vec![Pattern::Var("x".to_string())], 1)],
        };
        match compile(m) {
            Decision::Leaf {
                body_id: 1,
                bindings,
                ..
            } => {
                assert_eq!(bindings, vec![("x".to_string(), SubjectRef::Var(Var(42)))]);
            }
            other => panic!("expected Leaf with x=Var(42) binding, got {:?}", other),
        }
    }

    #[test]
    fn tuple_arities_2_3_3_compile_to_switch_with_2_cases() {
        // ast_eval shape: {:num, n}, {:add, a, b}, {:mul, a, b}
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(
                    vec![Pattern::Tuple(vec![
                        sp(Pattern::Atom("num".to_string())),
                        sp(Pattern::Var("n".to_string())),
                    ])],
                    1,
                ),
                row(
                    vec![Pattern::Tuple(vec![
                        sp(Pattern::Atom("add".to_string())),
                        sp(Pattern::Var("a".to_string())),
                        sp(Pattern::Var("b".to_string())),
                    ])],
                    2,
                ),
                row(
                    vec![Pattern::Tuple(vec![
                        sp(Pattern::Atom("mul".to_string())),
                        sp(Pattern::Var("a".to_string())),
                        sp(Pattern::Var("b".to_string())),
                    ])],
                    3,
                ),
            ],
        };
        match compile(m) {
            Decision::Switch {
                kind: SwitchKind::TupleArity,
                cases,
                ..
            } => {
                assert_eq!(cases.len(), 2, "expected 2 arity cases");
                let arities: Vec<u32> = cases
                    .iter()
                    .map(|(k, _)| match k {
                        SwitchKey::Arity(n) => *n,
                        _ => panic!("expected Arity"),
                    })
                    .collect();
                assert!(arities.contains(&2));
                assert!(arities.contains(&3));
            }
            other => panic!("expected Switch on TupleArity, got {:?}", other),
        }
    }

    #[test]
    fn tuple_projection_bindings_are_explicit_subject_refs() {
        let m = Matrix {
            subjects: vec![Var(7)],
            rows: vec![row(
                vec![Pattern::Tuple(vec![
                    sp(Pattern::Atom("ok".to_string())),
                    sp(Pattern::Var("x".to_string())),
                ])],
                1,
            )],
        };

        let Decision::Switch {
            kind: SwitchKind::TupleArity,
            cases,
            ..
        } = compile(m)
        else {
            panic!("expected tuple-arity switch");
        };
        let (_, arity_2) = cases
            .into_iter()
            .find(|(key, _)| matches!(key, SwitchKey::Arity(2)))
            .expect("arity-2 case");
        let Decision::Switch { cases, .. } = arity_2 else {
            panic!("expected atom-head switch inside tuple arity case");
        };
        let (_, ok_case) = cases
            .into_iter()
            .find(|(key, _)| matches!(key, SwitchKey::AtomName(s) if s == "ok"))
            .expect("ok atom case");
        let Decision::Leaf { bindings, .. } = ok_case else {
            panic!("expected tuple field binding leaf");
        };

        assert_eq!(
            bindings,
            vec![(
                "x".to_string(),
                SubjectRef::TupleField {
                    tuple: Box::new(SubjectRef::Var(Var(7))),
                    index: 1,
                }
            )]
        );
    }

    #[test]
    fn bitstring_row_drops_to_per_row_fallback() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Bitstring(vec![])], 1),
                row(vec![Pattern::Wildcard], 2),
            ],
        };
        match compile(m) {
            Decision::PerRow { subject, row, on_fail } => {
                assert_eq!(subject, SubjectRef::Var(Var(0)));
                assert_eq!(row.body_id, 1);
                match *on_fail {
                    Decision::Leaf { body_id: 2, .. } => {}
                    other => panic!("expected bitstring miss to continue to row 2, got {:?}", other),
                }
            }
            other => panic!("expected PerRow for bitstring, got {:?}", other),
        }
    }

    #[test]
    fn map_row_drops_to_per_row_fallback() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Map(vec![])], 1),
                row(vec![Pattern::Wildcard], 2),
            ],
        };
        match compile(m) {
            Decision::PerRow { subject, row, on_fail } => {
                assert_eq!(subject, SubjectRef::Var(Var(0)));
                assert_eq!(row.body_id, 1);
                match *on_fail {
                    Decision::Leaf { body_id: 2, .. } => {}
                    other => panic!("expected map miss to continue to row 2, got {:?}", other),
                }
            }
            other => panic!("expected PerRow for map, got {:?}", other),
        }
    }

    #[test]
    fn per_row_preserves_row_order_after_earlier_fallback() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Map(vec![])], 10),
                row(vec![Pattern::Bitstring(vec![])], 11),
                row(vec![Pattern::Wildcard], 12),
            ],
        };

        match compile(m) {
            Decision::PerRow {
                row,
                on_fail: first_fail,
                ..
            } => {
                assert_eq!(row.body_id, 10);
                match *first_fail {
                    Decision::PerRow {
                        row,
                        on_fail: second_fail,
                        ..
                    } => {
                        assert_eq!(row.body_id, 11);
                        match *second_fail {
                            Decision::Leaf { body_id: 12, .. } => {}
                            other => panic!("expected final wildcard row, got {:?}", other),
                        }
                    }
                    other => panic!("expected second PerRow fallback, got {:?}", other),
                }
            }
            other => panic!("expected PerRow chain, got {:?}", other),
        }
    }

    #[test]
    fn guarded_row_carries_guard_in_leaf() {
        use crate::ast::Expr;
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![Row {
                patterns: vec![sp(Pattern::Wildcard)],
                preconditions: Vec::new(),
                guard: Some(sp(Expr::Bool(true))),
                body_id: 5,
            }],
        };
        match compile(m) {
            Decision::Leaf {
                body_id: 5,
                guard: Some(_),
                on_guard_fail: Some(_),
                ..
            } => {}
            other => panic!("expected guarded leaf, got {:?}", other),
        }
    }

    #[test]
    fn guarded_row_rejects_to_next_reachable_row() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row_with_guard(vec![Pattern::Wildcard], 0),
                row(vec![Pattern::Wildcard], 1),
            ],
        };

        match compile(m) {
            Decision::Leaf {
                body_id: 0,
                on_guard_fail: Some(reject),
                ..
            } => match *reject {
                Decision::Leaf { body_id: 1, .. } => {}
                other => panic!("expected guard reject to reach body 1, got {:?}", other),
            },
            other => panic!("expected guarded first leaf, got {:?}", other),
        }
    }

    #[test]
    fn leaf_preserves_preconditions_before_guard_lowering() {
        use crate::types::Types;

        let mut types = crate::types::ConcreteTypes;
        let int_ty = types.int();
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![Row {
                patterns: vec![sp(Pattern::Var("x".to_string()))],
                preconditions: vec![(Var(0), int_ty.clone())],
                guard: None,
                body_id: 9,
            }],
        };

        match compile(m) {
            Decision::Leaf {
                body_id: 9,
                bindings,
                preconditions,
                ..
            } => {
                assert_eq!(bindings, vec![("x".to_string(), SubjectRef::Var(Var(0)))]);
                assert_eq!(preconditions, vec![(Var(0), int_ty)]);
            }
            other => panic!("expected precondition-preserving leaf, got {:?}", other),
        }
    }

    // ── fz-ul4.45 — exhaustiveness + unreachability ─────────────────────

    #[test]
    fn unreachable_row_after_wildcard_detected() {
        // Row 0 wildcard catches everything; row 1 unreachable.
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Wildcard], 0),
                row(vec![Pattern::Int(42)], 1),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert_eq!(dead, vec![1]);
    }

    #[test]
    fn unreachable_row_after_full_atom_cover() {
        // Two atoms exhaust... no, atom space is infinite via wildcard.
        // Just check: row 0 matches :a, row 1 is :a too (unreachable).
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Atom("a".to_string())], 0),
                row(vec![Pattern::Atom("a".to_string())], 1),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert_eq!(dead, vec![1]);
    }

    fn row_with_guard(patterns: Vec<Pattern>, body_id: BodyId) -> Row {
        Row {
            patterns: patterns.into_iter().map(sp).collect(),
            preconditions: Vec::new(),
            // Concrete guard placeholder — content unused by
            // find_unreachable_rows (it only checks .is_none()).
            guard: Some(sp(crate::ast::Expr::Bool(true))),
            body_id,
        }
    }

    /// fz-rcp.2 — a guarded row does NOT consume coverage. The row
    /// that follows it with the same pattern is reachable (the guard
    /// can reject at runtime).
    #[test]
    fn guarded_row_does_not_dominate_later_row() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row_with_guard(vec![Pattern::Wildcard], 0),
                row(vec![Pattern::Wildcard], 1),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert!(
            dead.is_empty(),
            "guarded row should not mark unguarded successor unreachable, got {:?}",
            dead
        );
    }

    /// An unguarded wildcard still dominates later rows. Sanity check
    /// the guard-aware path doesn't break the normal case.
    #[test]
    fn unguarded_wildcard_still_dominates() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row_with_guard(vec![Pattern::Wildcard], 0),
                row(vec![Pattern::Wildcard], 1),
                row(vec![Pattern::Int(42)], 2),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert_eq!(dead, vec![2], "row 2 should be unreachable past row 1");
    }

    /// A guarded row whose pattern is fully covered by an unguarded
    /// predecessor IS unreachable (the predecessor's pattern matches
    /// every value the guarded row could see).
    #[test]
    fn guarded_row_unreachable_under_unguarded_cover() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Wildcard], 0),
                row_with_guard(vec![Pattern::Wildcard], 1),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert_eq!(dead, vec![1]);
    }

    #[test]
    fn all_reachable_rows_no_warnings() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Int(0)], 0),
                row(vec![Pattern::Int(1)], 1),
                row(vec![Pattern::Wildcard], 2),
            ],
        };
        assert!(find_unreachable_rows(&m).is_empty());
    }

    #[test]
    fn distinct_utf8_binary_literals_are_reachable() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Binary(b"hi".to_vec())], 0),
                row(vec![Pattern::Binary(b"bye".to_vec())], 1),
                row(vec![Pattern::Wildcard], 2),
            ],
        };

        assert!(find_unreachable_rows(&m).is_empty());
        assert!(!is_inexhaustive(&m));
    }

    #[test]
    fn distinct_float_literals_are_reachable() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Float(1.5)], 0),
                row(vec![Pattern::Float(2.5)], 1),
                row(vec![Pattern::Wildcard], 2),
            ],
        };

        assert!(find_unreachable_rows(&m).is_empty());
        assert!(!is_inexhaustive(&m));
    }

    #[test]
    fn duplicate_float_literal_is_unreachable() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Float(1.5)], 0),
                row(vec![Pattern::Float(1.5)], 1),
            ],
        };

        assert_eq!(find_unreachable_rows(&m), vec![1]);
    }

    #[test]
    fn duplicate_utf8_binary_literal_is_unreachable() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Binary(b"hi".to_vec())], 0),
                row(vec![Pattern::Binary(b"hi".to_vec())], 1),
            ],
        };

        assert_eq!(find_unreachable_rows(&m), vec![1]);
    }

    #[test]
    fn utf8_binary_literals_without_wildcard_are_inexhaustive() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Binary(b"hi".to_vec())], 0),
                row(vec![Pattern::Binary(b"bye".to_vec())], 1),
            ],
        };

        assert!(is_inexhaustive(&m));
    }

    #[test]
    fn inexhaustive_no_wildcard_flagged() {
        // Two specific ints, no wildcard → default reaches Fail.
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(vec![Pattern::Int(0)], 0), row(vec![Pattern::Int(1)], 1)],
        };
        assert!(is_inexhaustive(&m));
    }

    #[test]
    fn exhaustive_with_wildcard_not_flagged() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Int(0)], 0),
                row(vec![Pattern::Wildcard], 1),
            ],
        };
        assert!(!is_inexhaustive(&m));
    }

    #[test]
    fn empty_list_and_cons_exhaust_list_domain() {
        let cons = Pattern::List(
            vec![sp(Pattern::Var("h".to_string()))],
            Some(Box::new(sp(Pattern::Var("t".to_string())))),
        );
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::List(vec![], None)], 0),
                row(vec![cons], 1),
            ],
        };
        assert!(!is_inexhaustive_with_domains(&m, &[SubjectDomain::List]));
    }

    #[test]
    fn empty_list_and_cons_do_not_exhaust_any_domain() {
        let cons = Pattern::List(
            vec![sp(Pattern::Var("h".to_string()))],
            Some(Box::new(sp(Pattern::Var("t".to_string())))),
        );
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::List(vec![], None)], 0),
                row(vec![cons], 1),
            ],
        };
        assert!(is_inexhaustive_with_domains(&m, &[SubjectDomain::Any]));
    }
}
