use super::*;
use crate::source::SourceVersion;

fn span(start: u32, end: u32) -> Span {
    Span::new(SourceVersion::from_index(0), start, end)
}

#[test]
fn redundant_clause_diagnostic_names_the_matching_clause_by_line() {
    let diagnostic = redundant_clause_diagnostic(span(10, 20), 3);

    assert_eq!(diagnostic.code, codes::TYPE_REDUNDANT_CLAUSE);
    assert_eq!(
        diagnostic.message,
        "this clause cannot match because a previous clause at line 3 always matches"
    );
    assert_eq!(diagnostic.primary.span, span(10, 20));
    assert_eq!(diagnostic.primary.label, "unreachable");
}

#[test]
fn protocol_missing_callback_diagnostic_names_the_protocol_and_impl() {
    let diagnostic = protocol_missing_callback_diagnostic(span(5, 25), "each", 1, "P", "P.List", None);

    assert_eq!(diagnostic.code, codes::PROTOCOL_MISSING_CALLBACK);
    assert_eq!(
        diagnostic.message,
        "function each/1 required by protocol P is not implemented (in module P.List)"
    );
    assert_eq!(diagnostic.primary.span, span(5, 25));
    assert!(diagnostic.notes.is_empty());
}

#[test]
fn protocol_missing_callback_diagnostic_names_the_other_arity_when_one_exists() {
    let diagnostic = protocol_missing_callback_diagnostic(span(5, 25), "each", 1, "P", "P.List", Some(2));

    assert_eq!(diagnostic.notes, vec!["P.List defines each/2 instead".to_string()]);
}

#[test]
fn not_a_protocol_diagnostic_matches_elixirs_wording() {
    let diagnostic = not_a_protocol_diagnostic(span(5, 25), "Foo");

    assert_eq!(diagnostic.code, codes::RESOLVE_NOT_A_PROTOCOL);
    assert_eq!(diagnostic.message, "Foo is not a protocol");
    assert_eq!(diagnostic.primary.span, span(5, 25));
}
