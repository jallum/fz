use super::*;
use crate::ast::{FnClause, Pattern, TypeExprBody};

fn function_warnings(surface: &FunctionSurface) -> Vec<Diagnostic> {
    let mut resolver = |_callee: &crate::ast::Callee, _arity: usize| Ok(None);
    super::function_warnings(surface, &mut resolver)
}

fn function_surface(clauses: Vec<FnClause>) -> FunctionSurface {
    FunctionSurface {
        name: "main".to_string(),
        name_span: Span::DUMMY,
        clauses,
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

fn surface(body: Spanned<Expr>) -> FunctionSurface {
    function_surface(vec![fn_clause(Vec::new(), body)])
}

fn fn_clause(params: Vec<Spanned<Pattern>>, body: Spanned<Expr>) -> FnClause {
    FnClause {
        param_annotations: vec![None; params.len()],
        params,
        guard: None,
        body,
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
fn single_clause_function_head_does_not_warn() {
    let surface = function_surface(vec![fn_clause(
        vec![Spanned::dummy(Pattern::List(Vec::new(), None))],
        Spanned::dummy(Expr::Int(1)),
    )]);

    assert!(function_warnings(&surface).is_empty());
}

#[test]
fn partial_multi_clause_function_heads_warn() {
    let surface = function_surface(vec![
        fn_clause(
            vec![Spanned::dummy(Pattern::Atom("empty".to_string()))],
            Spanned::dummy(Expr::Atom("empty".to_string())),
        ),
        fn_clause(
            vec![Spanned::dummy(Pattern::Tuple(vec![
                Spanned::dummy(Pattern::Atom("node".to_string())),
                Spanned::dummy(Pattern::Var("left".to_string())),
                Spanned::dummy(Pattern::Var("value".to_string())),
                Spanned::dummy(Pattern::Var("right".to_string())),
            ]))],
            Spanned::dummy(Expr::Var("value".to_string())),
        ),
    ]);

    let warnings = function_warnings(&surface);
    assert_eq!(warnings.len(), 1);
    assert_eq!(warnings[0].code, codes::TYPE_NO_MATCHING_CLAUSE);
    assert_eq!(warnings[0].message, "function clauses don't cover every input");
    assert_eq!(warnings[0].primary.label, "the last clause is here");
    assert_eq!(
        warnings[0].notes,
        vec!["an input matched by no clause halts with `:function_clause` at runtime"]
    );
}

#[test]
fn total_multi_clause_function_heads_do_not_warn() {
    let surface = function_surface(vec![
        fn_clause(
            vec![Spanned::dummy(Pattern::Atom("ok".to_string()))],
            Spanned::dummy(Expr::Int(1)),
        ),
        fn_clause(vec![Spanned::dummy(Pattern::Wildcard)], Spanned::dummy(Expr::Int(0))),
    ]);

    assert!(function_warnings(&surface).is_empty());
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
