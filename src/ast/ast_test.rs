use super::{Expr, FnClause, FnDef, Spanned, TypeExprBody};
use crate::compiler::source::Span;

#[test]
fn fn_def_arity_uses_first_clause_for_regular_functions() {
    let def = fn_def(vec![
        FnClause {
            params: vec![
                Spanned::dummy(super::Pattern::Var("left".to_string())),
                Spanned::dummy(super::Pattern::Var("right".to_string())),
            ],
            param_annotations: vec![],
            guard: None,
            body: Spanned::dummy(Expr::Int(42)),
            span: Span::DUMMY,
        },
        FnClause {
            params: vec![],
            param_annotations: vec![],
            guard: None,
            body: Spanned::dummy(Expr::Int(0)),
            span: Span::DUMMY,
        },
    ]);

    assert_eq!(def.arity(), 2);
}

#[test]
fn fn_def_arity_uses_extern_params_for_extern_functions() {
    let mut def = fn_def(Vec::new());
    def.extern_abi = Some("C".to_string());
    def.extern_params = vec!["cstring".to_string(), "integer".to_string()];

    assert_eq!(def.arity(), 2);
}

#[test]
#[should_panic(expected = "functions should have at least one clause")]
fn fn_def_arity_panics_for_regular_function_without_clauses() {
    let def = fn_def(Vec::new());

    let _ = def.arity();
}

fn fn_def(clauses: Vec<FnClause>) -> FnDef {
    FnDef {
        name: "arity_subject".to_string(),
        name_span: Span::DUMMY,
        clauses,
        is_macro: false,
        is_private: false,
        extern_abi: None,
        extern_params: Vec::new(),
        extern_ret_tokens: TypeExprBody(Vec::new()),
        variadic: false,
        attrs: Vec::new(),
        span: Span::DUMMY,
    }
}
