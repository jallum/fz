use crate::ast::{Expr, MatchClause, Spanned, WithBinding};
use crate::compiler::source::Span;
use crate::diag::{Diagnostic, codes};
use crate::dispatch_matrix::pattern::{PatternBodyId, PatternRow, SourcePatternRows, is_inexhaustive_with_domains};
use crate::function_surface::FunctionSurface;

use super::types::Ty;

pub(crate) fn function_warnings(surface: &FunctionSurface) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    for clause in &surface.clauses {
        if let Some(guard) = &clause.guard {
            walk_expr(guard, &mut diagnostics);
        }
        walk_expr(&clause.body, &mut diagnostics);
    }
    diagnostics
}

fn walk_expr(expr: &Spanned<Expr>, diagnostics: &mut Vec<Diagnostic>) {
    match &expr.node {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Var(_)
        | Expr::FnRef { .. }
        | Expr::CaptureArg(_)
        | Expr::Quote(_)
        | Expr::Unquote(_) => {}
        Expr::Capture(body) => walk_expr(body, diagnostics),
        Expr::List(elems, tail) => {
            elems.iter().for_each(|elem| walk_expr(elem, diagnostics));
            if let Some(tail) = tail {
                walk_expr(tail, diagnostics);
            }
        }
        Expr::Tuple(elems) => elems.iter().for_each(|elem| walk_expr(elem, diagnostics)),
        Expr::Bitstring(fields) => fields.iter().for_each(|field| walk_expr(&field.value, diagnostics)),
        Expr::Map(entries) => {
            for (key, value) in entries {
                walk_expr(key, diagnostics);
                walk_expr(value, diagnostics);
            }
        }
        Expr::MapUpdate(base, entries) => {
            walk_expr(base, diagnostics);
            for (key, value) in entries {
                walk_expr(key, diagnostics);
                walk_expr(value, diagnostics);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, value) in fields {
                walk_expr(value, diagnostics);
            }
        }
        Expr::Index(base, key) => {
            walk_expr(base, diagnostics);
            walk_expr(key, diagnostics);
        }
        Expr::Call(target, args) | Expr::ClosureCall(target, args) => {
            walk_expr(target, diagnostics);
            args.iter().for_each(|arg| walk_expr(arg, diagnostics));
        }
        Expr::Ascribe(value, _) | Expr::UnOp(_, value) | Expr::Match(_, value) => walk_expr(value, diagnostics),
        Expr::BinOp(_, left, right) => {
            walk_expr(left, diagnostics);
            walk_expr(right, diagnostics);
        }
        Expr::If(cond, then_expr, else_expr) => {
            walk_expr(cond, diagnostics);
            walk_expr(then_expr, diagnostics);
            if let Some(else_expr) = else_expr {
                walk_expr(else_expr, diagnostics);
            }
        }
        Expr::Case(subject, clauses) => {
            if let Some(subject) = subject {
                walk_expr(subject, diagnostics);
            }
            check_match_clauses(expr.span, "case", "case_clause", clauses, diagnostics);
            walk_match_clause_bodies(clauses, diagnostics);
        }
        Expr::Cond(arms) => {
            for (test, body) in arms {
                walk_expr(test, diagnostics);
                walk_expr(body, diagnostics);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Bare(value) | WithBinding::Match(_, value) => walk_expr(value, diagnostics),
                }
            }
            walk_expr(body, diagnostics);
            check_match_clauses(expr.span, "with else", "with_clause", else_clauses, diagnostics);
            walk_match_clause_bodies(else_clauses, diagnostics);
        }
        Expr::Receive { clauses, after } => {
            walk_match_clause_bodies(clauses, diagnostics);
            if let Some(after) = after {
                walk_expr(&after.timeout, diagnostics);
                walk_expr(&after.body, diagnostics);
            }
        }
        Expr::Block(items) => items.iter().for_each(|item| walk_expr(item, diagnostics)),
        Expr::Lambda(clauses) => {
            for clause in clauses {
                if let Some(guard) = &clause.guard {
                    walk_expr(guard, diagnostics);
                }
                walk_expr(&clause.body, diagnostics);
            }
        }
    }
}

fn walk_match_clause_bodies(clauses: &[MatchClause], diagnostics: &mut Vec<Diagnostic>) {
    for clause in clauses {
        if let Some(guard) = &clause.guard {
            walk_expr(guard, diagnostics);
        }
        walk_expr(&clause.body, diagnostics);
    }
}

fn check_match_clauses(
    span: Span,
    construct: &str,
    halt_atom: &str,
    clauses: &[MatchClause],
    diagnostics: &mut Vec<Diagnostic>,
) {
    if clauses.is_empty() || clauses.iter().any(|clause| clause.guard.is_some()) {
        return;
    }
    let rows = clauses
        .iter()
        .enumerate()
        .map(|(index, clause)| PatternRow::<Ty> {
            patterns: vec![clause.pattern.clone()],
            preconditions: Vec::new(),
            guard: None,
            body_id: index as PatternBodyId,
        })
        .collect();
    let source_patterns = SourcePatternRows { input_count: 1, rows };
    if is_inexhaustive_with_domains(&source_patterns, &[]) {
        diagnostics.push(inexhaustive_diag_at(span, construct, halt_atom));
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{FnClause, Pattern, TypeExprBody};

    fn surface(body: Spanned<Expr>) -> FunctionSurface {
        FunctionSurface {
            name: "main".to_string(),
            name_span: Span::DUMMY,
            clauses: vec![FnClause {
                params: Vec::new(),
                param_annotations: Vec::new(),
                guard: None,
                body,
                span: Span::DUMMY,
            }],
            is_macro: false,
            extern_abi: None,
            extern_param_tokens: Vec::new(),
            extern_ret_tokens: TypeExprBody(Vec::new()),
            extern_constraints: Vec::new(),
            variadic: false,
            attrs: Vec::new(),
            span: Span::DUMMY,
        }
    }

    #[test]
    fn total_case_does_not_warn() {
        let body = Spanned::dummy(Expr::Case(
            Some(Box::new(Spanned::dummy(Expr::Var("x".to_string())))),
            vec![MatchClause {
                pattern: Spanned::dummy(Pattern::Wildcard),
                guard: None,
                body: Spanned::dummy(Expr::Int(0)),
                span: Span::DUMMY,
            }],
        ));

        assert!(function_warnings(&surface(body)).is_empty());
    }

    #[test]
    fn partial_case_warns() {
        let body = Spanned::dummy(Expr::Case(
            Some(Box::new(Spanned::dummy(Expr::Var("x".to_string())))),
            vec![MatchClause {
                pattern: Spanned::dummy(Pattern::Atom("ok".to_string())),
                guard: None,
                body: Spanned::dummy(Expr::Int(1)),
                span: Span::DUMMY,
            }],
        ));

        let warnings = function_warnings(&surface(body));
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].code, codes::TYPE_NO_MATCHING_CLAUSE);
        assert_eq!(warnings[0].message, "`case` clauses don't cover every input");
    }

    #[test]
    fn partial_with_else_warns() {
        let body = Spanned::dummy(Expr::With(
            vec![WithBinding::Match(
                Spanned::dummy(Pattern::Atom("ok".to_string())),
                Spanned::dummy(Expr::Var("x".to_string())),
            )],
            Box::new(Spanned::dummy(Expr::Int(1))),
            vec![MatchClause {
                pattern: Spanned::dummy(Pattern::Atom("err".to_string())),
                guard: None,
                body: Spanned::dummy(Expr::Int(0)),
                span: Span::DUMMY,
            }],
        ));

        let warnings = function_warnings(&surface(body));
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].code, codes::TYPE_NO_MATCHING_CLAUSE);
        assert_eq!(warnings[0].message, "`with else` clauses don't cover every input");
    }

    #[test]
    fn guarded_case_exhaustiveness_is_deferred() {
        let body = Spanned::dummy(Expr::Case(
            Some(Box::new(Spanned::dummy(Expr::Var("x".to_string())))),
            vec![MatchClause {
                pattern: Spanned::dummy(Pattern::Var("x".to_string())),
                guard: Some(Spanned::dummy(Expr::Bool(true))),
                body: Spanned::dummy(Expr::Int(1)),
                span: Span::DUMMY,
            }],
        ));

        assert!(function_warnings(&surface(body)).is_empty());
    }
}
