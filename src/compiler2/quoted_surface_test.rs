use super::quoted_surface::{ScopeForm, SurfaceSourceContext, read_protocol_impl_body_surface, read_scope_surface};
use super::{CodeMap, parse_quoted_program};
use crate::telemetry::ConfiguredTelemetry;

#[test]
fn compiler2_quoted_surface_groups_multiclause_functions_into_one_logical_form() {
    let tel = ConfiguredTelemetry::new();
    let source = "fn alpha(0), do: 0\nfn beta(x), do: x\nfn alpha(x), do: x\n";
    let mut code = CodeMap::new();
    let code_id = code.define(Some("surface.fz".to_string()), source.to_string());
    let root = parse_quoted_program("surface.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source, &tel);

    let surface = read_scope_surface(&root, &ctx).expect("surface read");

    assert_eq!(
        surface.forms.len(),
        2,
        "quoted surface grouping should produce one logical form per function, not per clause",
    );
    match &surface.forms[0] {
        ScopeForm::Function(form) => {
            assert_eq!(form.name, "alpha");
            assert_eq!(form.arity, 1);
            assert_eq!(
                form.source
                    .cursor()
                    .list_items()
                    .expect("alpha grouped source items")
                    .len(),
                2,
                "multi-clause function source should be one grouped quoted list carrying both clauses",
            );
        }
        other => panic!("first grouped form should be alpha/1, got {other:?}"),
    }
    match &surface.forms[1] {
        ScopeForm::Function(form) => {
            assert_eq!(form.name, "beta");
            assert_eq!(form.arity, 1);
            assert_eq!(
                form.source
                    .cursor()
                    .list_items()
                    .expect("beta grouped source items")
                    .len(),
                1,
                "single-clause functions should still use the same grouped-source shape",
            );
        }
        other => panic!("second grouped form should be beta/1, got {other:?}"),
    }

    let surface_again = read_scope_surface(&root, &ctx).expect("surface reread");
    match (&surface.forms[0], &surface_again.forms[0]) {
        (ScopeForm::Function(first), ScopeForm::Function(second)) => {
            assert_eq!(
                first.source.key(),
                second.source.key(),
                "re-reading the same quoted source should reuse the same grouped function root",
            );
        }
        pair => panic!("expected alpha grouped function on reread, got {pair:?}"),
    }
}

#[test]
fn compiler2_quoted_surface_keeps_attached_function_attrs_inside_grouped_source() {
    let tel = ConfiguredTelemetry::new();
    let source = "@doc \"alpha\"\n@spec alpha(integer) :: integer\nfn alpha(x), do: x\n";
    let mut code = CodeMap::new();
    let code_id = code.define(Some("surface.fz".to_string()), source.to_string());
    let root = parse_quoted_program("surface.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source, &tel);

    let surface = read_scope_surface(&root, &ctx).expect("surface read");

    match &surface.forms[0] {
        ScopeForm::Function(form) => {
            assert_eq!(form.name, "alpha");
            assert_eq!(form.arity, 1);
            let items = form
                .source
                .cursor()
                .list_items()
                .expect("grouped function source items");
            assert_eq!(
                items.len(),
                3,
                "grouped function source should carry attrs plus the clause"
            );
            assert_eq!(
                items[0]
                    .ast_node()
                    .expect("doc cursor")
                    .expect("doc node")
                    .head
                    .atom_name()
                    .expect("doc head"),
                "@doc"
            );
            assert_eq!(
                items[1]
                    .ast_node()
                    .expect("spec cursor")
                    .expect("spec node")
                    .head
                    .atom_name()
                    .expect("spec head"),
                "@spec"
            );
            assert_eq!(
                items[2]
                    .ast_node()
                    .expect("fn cursor")
                    .expect("fn node")
                    .head
                    .atom_name()
                    .expect("fn head"),
                "fn"
            );
        }
        other => panic!("expected grouped alpha function, got {other:?}"),
    }
}

#[test]
fn compiler2_quoted_surface_reads_protocol_impl_callbacks_through_grouped_source() {
    let tel = ConfiguredTelemetry::new();
    let source = "defimpl String.Chars, for: Box do\n  @doc \"box\"\n  fn to_string(%Box{value: 0}), do: \"zero\"\n  fn to_string(%Box{value: value}), do: value\nend\n";
    let mut code = CodeMap::new();
    let code_id = code.define(Some("surface.fz".to_string()), source.to_string());
    let root = parse_quoted_program("surface.fz", source, &tel).expect("quoted parse");
    let ctx = SurfaceSourceContext::new(code_id, source, &tel);

    let surface = read_scope_surface(&root, &ctx).expect("surface read");

    match &surface.forms[0] {
        ScopeForm::ProtocolImpl(form) => {
            let body = read_protocol_impl_body_surface(form, &ctx).expect("protocol impl body surface");
            assert_eq!(
                body.forms.len(),
                1,
                "callback clauses should group to one logical function surface"
            );
            match &body.forms[0] {
                ScopeForm::Function(function) => {
                    assert_eq!(function.name, "to_string");
                    assert_eq!(function.arity, 1);
                    let items = function.source.cursor().list_items().expect("callback grouped items");
                    assert_eq!(
                        items.len(),
                        3,
                        "grouped callback source should carry attrs plus both clauses"
                    );
                }
                other => panic!("expected grouped callback function, got {other:?}"),
            }
        }
        other => panic!("expected protocol impl form, got {other:?}"),
    }
}
