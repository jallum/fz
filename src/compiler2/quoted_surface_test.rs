use super::parse_quoted_program;
use super::quoted_surface::{ScopeForm, read_scope_surface};
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::ConfiguredTelemetry;

#[test]
fn compiler2_quoted_surface_groups_multiclause_functions_like_legacy_items() {
    let tel = ConfiguredTelemetry::new();
    let source = "fn alpha(0), do: 0\nfn beta(x), do: x\nfn alpha(x), do: x\n";
    let root = parse_quoted_program("surface.fz", source, &tel).expect("quoted parse");
    let tokens = Lexer::with_source_name(source, "surface.fz")
        .tokenize(&tel)
        .expect("legacy lex");
    let program = Parser::new(tokens).parse_program(&tel).expect("legacy parse");

    let surface = read_scope_surface(&root, &program.items, &program.attrs).expect("surface read");

    assert_eq!(
        surface.forms.len(),
        2,
        "quoted surface grouping should match the legacy item inventory, not the raw clause count",
    );
    match &surface.forms[0] {
        ScopeForm::Function(form) => {
            assert_eq!(form.legacy_fn.name, "alpha");
            assert_eq!(form.legacy_fn.clauses.len(), 2);
        }
        other => panic!("first grouped form should be alpha/1, got {other:?}"),
    }
    match &surface.forms[1] {
        ScopeForm::Function(form) => {
            assert_eq!(form.legacy_fn.name, "beta");
            assert_eq!(form.legacy_fn.clauses.len(), 1);
        }
        other => panic!("second grouped form should be beta/1, got {other:?}"),
    }
}
