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
