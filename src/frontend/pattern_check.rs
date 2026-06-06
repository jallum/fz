//! fz-ul4.45 — Pattern-match correctness analysis.
//!
//! Walks the program's AST, finds every match site (multi-clause `fn`,
//! `case` expression, `with`'s `else` cascade), builds a `SourcePatternRows` from
//! its clauses, and runs `dispatch_matrix::pattern::find_unreachable_rows` and
//! `is_inexhaustive`. Emits a `Diagnostic` per finding.
//!
//! Pipeline position: runs alongside `spec_check::validate_specs` after
//! lower_program; both pure analysis, both non-fatal, both feed the
//! driver's render-and-exit logic.

use crate::ast::{Expr, FnClause, FnDef, Item, MatchClause, Pattern, Program, Spanned, WithBinding};
use crate::compiler::source::Span;
use crate::diag::{Diagnostic, codes};
use crate::dispatch_matrix::pattern::{
    KnownSubjectDomain, PatternBodyId, PatternRow, SourcePatternRows, find_unreachable_rows,
    is_inexhaustive_with_domains,
};
use crate::fz_ir::Var;
use crate::types::Types;
use std::collections::{HashMap, HashSet};

/// Walk `prog` and return one `Diagnostic` per unreachable clause and
/// per inexhaustive match. Empty when everything checks.
///
/// `survivors` is the set of `(name, arity)` pairs for fns whose body remains
/// semantically reachable in the executable `ModulePlan`. Pattern concerns
/// inside an unreachable fn are dead-code questions: the `:function_clause`
/// halt the inexhaustive warning worries about can only fire from a body that
/// still exists at runtime. Pass `None` to warn for every fn (used by unit
/// tests that don't build a plan).
pub fn check_program<T: Types>(
    _t: &mut T,
    prog: &Program,
    survivors: Option<&HashSet<(String, usize)>>,
    domains: Option<&HashMap<(String, usize), Vec<KnownSubjectDomain>>>,
) -> Vec<Diagnostic> {
    let mut diags: Vec<Diagnostic> = Vec::new();
    for item in &prog.items {
        if let Item::Fn(fn_def) = &**item {
            let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
            let emitted = survivors
                .map(|s| s.contains(&(fn_def.name.clone(), arity)))
                .unwrap_or(true);
            if !emitted {
                continue;
            }
            let fn_domains = domains.and_then(|d| d.get(&(fn_def.name.clone(), arity)));
            check_fn_def(fn_def, fn_domains.map(Vec::as_slice), &mut diags);
        }
    }
    diags
}

fn check_fn_def(fn_def: &FnDef, domains: Option<&[KnownSubjectDomain]>, diags: &mut Vec<Diagnostic>) {
    if fn_def.clauses.len() > 1 {
        check_fn_clauses(fn_def, domains, diags);
    }
    for clause in &fn_def.clauses {
        if let Some(g) = &clause.guard {
            walk_expr(g, diags);
        }
        walk_expr(&clause.body, diags);
    }
}

/// Multi-clause `fn` heads. SourcePatternRows has one column per parameter; rows
/// are the clauses' parameter lists. Inexhaustive matches halt with
/// `:function_clause` at runtime — surfacing as a warning gives an
/// early signal.
fn check_fn_clauses(fn_def: &FnDef, domains: Option<&[KnownSubjectDomain]>, diags: &mut Vec<Diagnostic>) {
    let arity = fn_def.clauses[0].params.len();
    let subjects: Vec<Var> = (0..arity as u32).map(Var).collect();
    let rows: Vec<PatternRow> = fn_def
        .clauses
        .iter()
        .enumerate()
        .map(|(i, c)| PatternRow {
            patterns: c.params.clone(),
            preconditions: Vec::new(),
            guard: c.guard.clone(),
            body_id: i as PatternBodyId,
        })
        .collect();
    let source_patterns = SourcePatternRows { subjects, rows };

    // Type-ascribed params (`x :: integer`) and clause guards add match
    // constraints the SourcePatternRows does not model — it sees an ascribed or
    // guarded param as a plain binding (catch-all). Its first-match coverage
    // verdict is therefore unsound when either is present: a later clause can be
    // reachable for inputs the ascribed/guarded clause rejects (e.g.
    // `check(x :: integer)` then `check(x)` — the second catches non-integers).
    // Both reachability and exhaustiveness reporting are gated on neither being
    // present. Modeling the constraints in the matrix is future work (fz-ldj).
    let any_guard = fn_def.clauses.iter().any(|c| c.guard.is_some());
    let any_annot = fn_def
        .clauses
        .iter()
        .any(|c| c.param_annotations.iter().any(|a| a.is_some()));
    if any_guard || any_annot {
        return;
    }

    for dead_id in find_unreachable_rows(&source_patterns) {
        let dead = &fn_def.clauses[dead_id as usize];
        diags.push(unreachable_clause_diag(dead, &fn_def.clauses[..dead_id as usize], "fn"));
    }

    let domain_slice = domains.unwrap_or(&[]);
    if is_inexhaustive_with_domains(&source_patterns, domain_slice) {
        let last = fn_def.clauses.last().unwrap();
        diags.push(inexhaustive_diag(fn_def, last.span, "fn", "function_clause"));
    }
}

fn check_case_clauses(case_span: Span, clauses: &[MatchClause], diags: &mut Vec<Diagnostic>) {
    if clauses.is_empty() {
        return;
    }
    let subjects = vec![Var(0)];
    let rows: Vec<PatternRow> = clauses
        .iter()
        .enumerate()
        .map(|(i, c)| PatternRow {
            patterns: vec![c.pattern.clone()],
            preconditions: Vec::new(),
            guard: c.guard.clone(),
            body_id: i as PatternBodyId,
        })
        .collect();
    let source_patterns = SourcePatternRows { subjects, rows };

    for dead_id in find_unreachable_rows(&source_patterns) {
        let dead = &clauses[dead_id as usize];
        diags.push(unreachable_clause_diag_match(
            dead,
            &clauses[..dead_id as usize],
            "case",
        ));
    }

    let any_guard = clauses.iter().any(|c| c.guard.is_some());
    if !any_guard && is_inexhaustive_with_domains(&source_patterns, &[]) {
        diags.push(inexhaustive_diag_at(case_span, "case", "case_clause"));
    }
}

fn check_with_else(with_span: Span, else_clauses: &[MatchClause], diags: &mut Vec<Diagnostic>) {
    // Empty else is fine — `with` without else halts on first mismatch.
    if else_clauses.is_empty() {
        return;
    }
    let subjects = vec![Var(0)];
    let rows: Vec<PatternRow> = else_clauses
        .iter()
        .enumerate()
        .map(|(i, c)| PatternRow {
            patterns: vec![c.pattern.clone()],
            preconditions: Vec::new(),
            guard: c.guard.clone(),
            body_id: i as PatternBodyId,
        })
        .collect();
    let source_patterns = SourcePatternRows { subjects, rows };
    for dead_id in find_unreachable_rows(&source_patterns) {
        let dead = &else_clauses[dead_id as usize];
        diags.push(unreachable_clause_diag_match(
            dead,
            &else_clauses[..dead_id as usize],
            "with else",
        ));
    }
    let any_guard = else_clauses.iter().any(|c| c.guard.is_some());
    if !any_guard && is_inexhaustive_with_domains(&source_patterns, &[]) {
        diags.push(inexhaustive_diag_at(with_span, "with else", "with_clause"));
    }
}

// ── walkers ────────────────────────────────────────────────────────────────

fn walk_expr(e: &Spanned<Expr>, diags: &mut Vec<Diagnostic>) {
    match &e.node {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Var(_)
        | Expr::FnRef { .. }
        // fz-g58.2.6 — `&N` is a leaf; the `&(...)` body is walked below.
        | Expr::CaptureArg(_)
        | Expr::Quote(_)
        | Expr::Unquote(_) => {}
        Expr::Capture(body) => walk_expr(body, diags),
        Expr::Block(items) => items.iter().for_each(|i| walk_expr(i, diags)),
        Expr::BinOp(_, a, b) => {
            walk_expr(a, diags);
            walk_expr(b, diags);
        }
        Expr::UnOp(_, x) | Expr::Match(_, x) | Expr::Ascribe(x, _) => walk_expr(x, diags),
        Expr::Index(a, b) => {
            walk_expr(a, diags);
            walk_expr(b, diags);
        }
        Expr::If(c, t, els) => {
            walk_expr(c, diags);
            walk_expr(t, diags);
            if let Some(e) = els {
                walk_expr(e, diags);
            }
        }
        Expr::Case(subj, clauses) => {
            if let Some(subj) = subj {
                walk_expr(subj, diags);
            }
            check_case_clauses(e.span, clauses, diags);
            for c in clauses {
                if let Some(g) = &c.guard {
                    walk_expr(g, diags);
                }
                walk_expr(&c.body, diags);
            }
        }
        Expr::Cond(arms) => {
            for (test, body) in arms {
                walk_expr(test, diags);
                walk_expr(body, diags);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for b in bindings {
                match b {
                    WithBinding::Bare(e) => walk_expr(e, diags),
                    WithBinding::Match(_, e) => walk_expr(e, diags),
                }
            }
            walk_expr(body, diags);
            check_with_else(e.span, else_clauses, diags);
            for c in else_clauses {
                if let Some(g) = &c.guard {
                    walk_expr(g, diags);
                }
                walk_expr(&c.body, diags);
            }
        }
        Expr::Lambda(clauses) => {
            for clause in clauses {
                if let Some(g) = &clause.guard {
                    walk_expr(g, diags);
                }
                walk_expr(&clause.body, diags);
            }
        }
        Expr::Call(target, args) | Expr::ClosureCall(target, args) => {
            walk_expr(target, diags);
            args.iter().for_each(|a| walk_expr(a, diags));
        }
        Expr::List(elems, tail) => {
            elems.iter().for_each(|e| walk_expr(e, diags));
            if let Some(t) = tail {
                walk_expr(t, diags);
            }
        }
        Expr::Tuple(elems) => {
            elems.iter().for_each(|e| walk_expr(e, diags));
        }
        Expr::Map(entries) | Expr::MapUpdate(_, entries) => {
            for (k, v) in entries {
                walk_expr(k, diags);
                walk_expr(v, diags);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, v) in fields {
                walk_expr(v, diags);
            }
        }
        Expr::Bitstring(fields) => fields.iter().for_each(|f| walk_expr(&f.value, diags)),
        // fz-5vj — receive has no scrutinee; just walk each clause's
        // guard + body and the after expr/body. Per-receive exhaustiveness
        // is intentionally not checked: unmatched messages stay in the
        // mailbox by design (selective receive).
        Expr::Receive { clauses, after } => {
            for c in clauses {
                if let Some(g) = &c.guard {
                    walk_expr(g, diags);
                }
                walk_expr(&c.body, diags);
            }
            if let Some(af) = after {
                walk_expr(&af.timeout, diags);
                walk_expr(&af.body, diags);
            }
        }
    }
}

// ── diagnostic builders ────────────────────────────────────────────────────

fn unreachable_clause_diag(dead: &FnClause, earlier: &[FnClause], construct: &str) -> Diagnostic {
    let mut d = Diagnostic::warning(
        codes::TYPE_UNREACHABLE_ARM,
        format!("this {} clause is unreachable", construct),
        dead.span,
    )
    .with_label("never matches — an earlier clause covers every input that reaches here");
    if let Some(catcher) = earlier
        .iter()
        .rev()
        .find(|c| all_wildlike(&c.params) && c.guard.is_none())
    {
        d = d.with_secondary(catcher.span, "this clause already catches every input");
        d = d.with_help("remove this clause, or reorder so the more specific pattern comes first");
    } else {
        d = d.with_note("earlier clauses' patterns together cover every value this clause could match");
    }
    d
}

fn unreachable_clause_diag_match(dead: &MatchClause, earlier: &[MatchClause], construct: &str) -> Diagnostic {
    let mut d = Diagnostic::warning(
        codes::TYPE_UNREACHABLE_ARM,
        format!("this {} clause is unreachable", construct),
        dead.span,
    )
    .with_label("never matches — an earlier clause covers every input that reaches here");
    if let Some(catcher) = earlier
        .iter()
        .rev()
        .find(|c| is_wildlike_pat(&c.pattern.node) && c.guard.is_none())
    {
        d = d.with_secondary(catcher.span, "this clause already catches every input");
        d = d.with_help("remove this clause, or reorder so the more specific pattern comes first");
    } else {
        d = d.with_note("earlier clauses' patterns together cover every value this clause could match");
    }
    d
}

fn inexhaustive_diag(fn_def: &FnDef, primary: Span, construct: &str, halt_atom: &str) -> Diagnostic {
    let _ = fn_def;
    Diagnostic::warning(
        codes::TYPE_NO_MATCHING_CLAUSE,
        format!("`{}` clauses don't cover every input", construct),
        primary,
    )
    .with_label("the last clause is here")
    .with_note(format!(
        "an input matched by no clause halts with `:{}` at runtime",
        halt_atom
    ))
    .with_help("add a wildcard clause `_ -> ...` to cover any remaining input")
}

fn inexhaustive_diag_at(primary: Span, construct: &str, halt_atom: &str) -> Diagnostic {
    Diagnostic::warning(
        codes::TYPE_NO_MATCHING_CLAUSE,
        format!("`{}` clauses don't cover every input", construct),
        primary,
    )
    .with_label("matched values may fall through here")
    .with_note(format!(
        "an input matched by no clause halts with `:{}` at runtime",
        halt_atom
    ))
    .with_help("add a wildcard clause `_ -> ...` to cover any remaining input")
}

// ── helpers ────────────────────────────────────────────────────────────────

fn all_wildlike(pats: &[Spanned<Pattern>]) -> bool {
    pats.iter().all(|p| is_wildlike_pat(&p.node))
}

fn is_wildlike_pat(p: &Pattern) -> bool {
    matches!(p, Pattern::Wildcard | Pattern::Var(_))
        || matches!(p, Pattern::As(_, inner) if is_wildlike_pat(&inner.node))
}

#[cfg(test)]
#[path = "pattern_check_test.rs"]
mod pattern_check_test;
