//! fz-ul4.45 — Pattern-match correctness analysis.
//!
//! Walks the program's AST, finds every match site (multi-clause `fn`,
//! `case` expression, `with`'s `else` cascade), builds a `Matrix` from
//! its clauses, and runs `pattern_matrix::find_unreachable_rows` and
//! `is_inexhaustive`. Emits a `Diagnostic` per finding.
//!
//! Pipeline position: runs alongside `spec_check::validate_specs` after
//! lower_program; both pure analysis, both non-fatal, both feed the
//! driver's render-and-exit logic.

use crate::ast::{
    Expr, FnClause, FnDef, Item, MatchClause, Pattern, Program, Spanned, WithBinding,
};
use crate::diag::{Diagnostic, codes};
use crate::fz_ir::Var;
use crate::pattern_matrix::{BodyId, Matrix, Row, find_unreachable_rows, is_inexhaustive};
use std::collections::HashSet;

/// Walk `prog` and return one `Diagnostic` per unreachable clause and
/// per inexhaustive match. Empty when everything checks.
///
/// `survivors` is the set of `(name, arity)` pairs for fns whose body
/// is actually emitted by codegen — i.e. survives the reducer. Pattern
/// concerns inside a fully-dissolved fn are dead-code questions: the
/// `:function_clause` halt the inexhaustive warning worries about can
/// only fire from a body that exists at runtime. Pass `None` to warn
/// for every fn (used by unit tests that don't run the reducer).
pub fn check_program(
    prog: &Program,
    survivors: Option<&HashSet<(String, usize)>>,
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
            check_fn_def(fn_def, &mut diags);
        }
    }
    diags
}

fn check_fn_def(fn_def: &FnDef, diags: &mut Vec<Diagnostic>) {
    if fn_def.clauses.len() > 1 {
        check_fn_clauses(fn_def, diags);
    }
    for clause in &fn_def.clauses {
        if let Some(g) = &clause.guard {
            walk_expr(g, diags);
        }
        walk_expr(&clause.body, diags);
    }
}

/// Multi-clause `fn` heads. Matrix has one column per parameter; rows
/// are the clauses' parameter lists. Inexhaustive matches halt with
/// `:function_clause` at runtime — surfacing as a warning gives an
/// early signal.
fn check_fn_clauses(fn_def: &FnDef, diags: &mut Vec<Diagnostic>) {
    let arity = fn_def.clauses[0].params.len();
    let subjects: Vec<Var> = (0..arity as u32).map(Var).collect();
    let rows: Vec<Row> = fn_def
        .clauses
        .iter()
        .enumerate()
        .map(|(i, c)| Row {
            patterns: c.params.clone(),
            preconditions: Vec::new(),
            guard: c.guard.clone(),
            body_id: i as BodyId,
        })
        .collect();
    let matrix = Matrix { subjects, rows };

    for dead_id in find_unreachable_rows(&matrix) {
        let dead = &fn_def.clauses[dead_id as usize];
        diags.push(unreachable_clause_diag(
            dead,
            &fn_def.clauses[..dead_id as usize],
            "fn",
        ));
    }

    // Skip exhaustiveness for fns with @spec preconditions or clause
    // guards — those decline first-match-wins coverage without invalidating
    // the source code. Future ticket: factor guards into the matrix
    // analysis. Multi-clause fns without guards/preconditions: every
    // multi-clause head needs a wildcard catch-all or a complete cover,
    // else `:function_clause` halt at runtime.
    let any_guard = fn_def.clauses.iter().any(|c| c.guard.is_some());
    let any_annot = fn_def
        .clauses
        .iter()
        .any(|c| c.param_annotations.iter().any(|a| a.is_some()));
    if !any_guard && !any_annot && is_inexhaustive(&matrix) {
        let last = fn_def.clauses.last().unwrap();
        diags.push(inexhaustive_diag(
            fn_def,
            last.span,
            "fn",
            "function_clause",
        ));
    }
}

fn check_case_clauses(
    case_span: crate::diag::Span,
    clauses: &[MatchClause],
    diags: &mut Vec<Diagnostic>,
) {
    if clauses.is_empty() {
        return;
    }
    let subjects = vec![Var(0)];
    let rows: Vec<Row> = clauses
        .iter()
        .enumerate()
        .map(|(i, c)| Row {
            patterns: vec![c.pattern.clone()],
            preconditions: Vec::new(),
            guard: c.guard.clone(),
            body_id: i as BodyId,
        })
        .collect();
    let matrix = Matrix { subjects, rows };

    for dead_id in find_unreachable_rows(&matrix) {
        let dead = &clauses[dead_id as usize];
        diags.push(unreachable_clause_diag_match(
            dead,
            &clauses[..dead_id as usize],
            "case",
        ));
    }

    let any_guard = clauses.iter().any(|c| c.guard.is_some());
    if !any_guard && is_inexhaustive(&matrix) {
        diags.push(inexhaustive_diag_at(case_span, "case", "case_clause"));
    }
}

fn check_with_else(
    with_span: crate::diag::Span,
    else_clauses: &[MatchClause],
    diags: &mut Vec<Diagnostic>,
) {
    // Empty else is fine — `with` without else halts on first mismatch.
    if else_clauses.is_empty() {
        return;
    }
    let subjects = vec![Var(0)];
    let rows: Vec<Row> = else_clauses
        .iter()
        .enumerate()
        .map(|(i, c)| Row {
            patterns: vec![c.pattern.clone()],
            preconditions: Vec::new(),
            guard: c.guard.clone(),
            body_id: i as BodyId,
        })
        .collect();
    let matrix = Matrix { subjects, rows };
    for dead_id in find_unreachable_rows(&matrix) {
        let dead = &else_clauses[dead_id as usize];
        diags.push(unreachable_clause_diag_match(
            dead,
            &else_clauses[..dead_id as usize],
            "with else",
        ));
    }
    let any_guard = else_clauses.iter().any(|c| c.guard.is_some());
    if !any_guard && is_inexhaustive(&matrix) {
        diags.push(inexhaustive_diag_at(with_span, "with else", "with_clause"));
    }
}

// ── walkers ────────────────────────────────────────────────────────────────

fn walk_expr(e: &Spanned<Expr>, diags: &mut Vec<Diagnostic>) {
    match &e.node {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Str(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Var(_)
        | Expr::FnRef { .. }
        | Expr::Quote(_)
        | Expr::Unquote(_) => {}
        Expr::Block(items) => items.iter().for_each(|i| walk_expr(i, diags)),
        Expr::BinOp(_, a, b) => {
            walk_expr(a, diags);
            walk_expr(b, diags);
        }
        Expr::UnOp(_, x) | Expr::Match(_, x) => walk_expr(x, diags),
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
            walk_expr(subj, diags);
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
        Expr::Lambda(_, body) => walk_expr(body, diags),
        Expr::Call(target, args) => {
            walk_expr(target, diags);
            args.iter().for_each(|a| walk_expr(a, diags));
        }
        Expr::List(elems, tail) => {
            elems.iter().for_each(|e| walk_expr(e, diags));
            if let Some(t) = tail {
                walk_expr(t, diags);
            }
        }
        Expr::Tuple(elems) | Expr::VecLit(_, elems) => {
            elems.iter().for_each(|e| walk_expr(e, diags));
        }
        Expr::Map(entries) | Expr::MapUpdate(_, entries) => {
            for (k, v) in entries {
                walk_expr(k, diags);
                walk_expr(v, diags);
            }
        }
        Expr::Bitstring(fields) => fields.iter().for_each(|f| walk_expr(&f.value, diags)),
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
        d = d.with_note(
            "earlier clauses' patterns together cover every value this clause could match",
        );
    }
    d
}

fn unreachable_clause_diag_match(
    dead: &MatchClause,
    earlier: &[MatchClause],
    construct: &str,
) -> Diagnostic {
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
        d = d.with_note(
            "earlier clauses' patterns together cover every value this clause could match",
        );
    }
    d
}

fn inexhaustive_diag(
    fn_def: &FnDef,
    primary: crate::diag::Span,
    construct: &str,
    halt_atom: &str,
) -> Diagnostic {
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

fn inexhaustive_diag_at(
    primary: crate::diag::Span,
    construct: &str,
    halt_atom: &str,
) -> Diagnostic {
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
mod tests {
    use super::*;
    use crate::parser::Parser;

    fn parse(src: &str) -> Program {
        let mut sm = crate::diag::SourceMap::new();
        let fid = sm.add_file("test.fz", src);
        let toks = crate::lexer::Lexer::with_file(src, fid).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        crate::resolve::flatten_modules(prog).unwrap()
    }

    #[test]
    fn detects_unreachable_after_wildcard_in_multi_clause_fn() {
        let prog = parse(
            "fn classify(_), do: :any\n\
             fn classify(0), do: :zero\n\
             fn main(), do: classify(7)",
        );
        let diags = check_program(&prog, None);
        assert!(
            diags.iter().any(|d| d.code == codes::TYPE_UNREACHABLE_ARM),
            "expected unreachable-arm diag, got {:?}",
            diags.iter().map(|d| d.code).collect::<Vec<_>>()
        );
    }

    #[test]
    fn detects_unreachable_after_wildcard_in_case() {
        let prog = parse(
            "fn f(v) do\n\
               case v do\n\
                 _ -> :any\n\
                 0 -> :zero\n\
               end\n\
             end\n\
             fn main(), do: f(7)",
        );
        let diags = check_program(&prog, None);
        assert!(diags.iter().any(|d| d.code == codes::TYPE_UNREACHABLE_ARM));
    }

    #[test]
    fn no_warning_when_specific_then_wildcard() {
        let prog = parse(
            "fn classify(0), do: :zero\n\
             fn classify(_), do: :other\n\
             fn main(), do: classify(7)",
        );
        let diags = check_program(&prog, None);
        assert!(
            diags.is_empty(),
            "should not warn when specific-then-wildcard: {:?}",
            diags.iter().map(|d| d.message.clone()).collect::<Vec<_>>()
        );
    }

    #[test]
    fn detects_inexhaustive_multi_clause_fn() {
        let prog = parse(
            "fn classify(0), do: :zero\n\
             fn classify(1), do: :one\n\
             fn main(), do: classify(7)",
        );
        let diags = check_program(&prog, None);
        assert!(
            diags
                .iter()
                .any(|d| d.code == codes::TYPE_NO_MATCHING_CLAUSE),
            "expected no-matching-clause diag, got {:?}",
            diags.iter().map(|d| d.code).collect::<Vec<_>>()
        );
    }

    #[test]
    fn detects_inexhaustive_case() {
        let prog = parse(
            "fn f(v) do\n\
               case v do\n\
                 0 -> :zero\n\
                 1 -> :one\n\
               end\n\
             end\n\
             fn main(), do: f(7)",
        );
        let diags = check_program(&prog, None);
        assert!(
            diags
                .iter()
                .any(|d| d.code == codes::TYPE_NO_MATCHING_CLAUSE)
        );
    }

    #[test]
    fn no_inexhaustive_with_wildcard() {
        let prog = parse(
            "fn classify(0), do: :zero\n\
             fn classify(_), do: :other\n\
             fn main(), do: classify(7)",
        );
        let diags = check_program(&prog, None);
        assert!(
            !diags
                .iter()
                .any(|d| d.code == codes::TYPE_NO_MATCHING_CLAUSE)
        );
    }
}
