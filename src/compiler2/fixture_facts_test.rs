use super::drive_test::assert_resolved;
use super::fixture_facts::{canonical_call_edge_facts, render_canonical_call_edge_snapshot};
use super::identity::ActivationKey;
use super::{CodeSubmission, Compiler2, ExecutableNeed, RootId, RootSubmission};
use crate::source::Span;
use crate::telemetry::ConfiguredTelemetry;

/// Drives a fixture to its backend product and renders its canonical
/// call-edge snapshot over the product-path activation inventory — the same
/// frontier the CLI semantic dump reads. Sourcing the inventory from the
/// product (rather than an ambient fact scan) is what surfaces
/// runtime-demand/callable-flow reached executables such as an escaped lambda
/// passed through an `f.(x)` boundary.
fn product_call_edge_snapshot(source: &str) -> String {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    let root = build_lambda_root(&mut compiler, source);
    let inventory = compiler
        .product_activation_inventory(root)
        .expect("compiler2 should settle a simple lambda fixture through the product path");
    render_canonical_call_edge_snapshot(&canonical_call_edge_facts(compiler.world(), root, &inventory))
}

fn build_lambda_root(compiler: &mut Compiler2<ConfiguredTelemetry>, source: &str) -> RootId {
    compiler.submit_code(CodeSubmission {
        name: Some("fixture.fz".to_string()),
        text: source.to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    })
}

#[test]
fn canonical_call_edge_facts_preserve_source_spans_and_hide_generated_ids() {
    let source = r#"
fn apply1(f, x), do: f.(x)

fn main() do
  add1 = fn x -> x + 1 end
  apply1(add1, 41)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    let root = build_lambda_root(&mut compiler, source);
    let inventory = compiler
        .product_activation_inventory(root)
        .expect("compiler2 should settle a simple lambda fixture through the product path");

    let facts = canonical_call_edge_facts(compiler.world(), root, &inventory);
    assert!(
        facts.iter().all(|fact| fact.callsite != "<generated>"),
        "user-authored callsites should retain their real source spans in canonical facts: {facts:?}",
    );

    let snapshot = render_canonical_call_edge_snapshot(&facts);
    assert!(
        !snapshot.contains("#lambda:"),
        "canonical labels should not leak raw generated function ids: {snapshot}",
    );
    assert!(
        snapshot.contains("::lambda[@"),
        "generated lambdas should still keep stable owner-relative provenance: {snapshot}",
    );
}

#[test]
fn canonical_call_edge_snapshots_are_stable_across_reruns() {
    let source = r#"
fn apply1(f, x), do: f.(x)

fn main() do
  add1 = fn x -> x + 1 end
  apply1(add1, 41)
end
"#;

    let first = product_call_edge_snapshot(source);
    let second = product_call_edge_snapshot(source);
    assert_eq!(
        first, second,
        "canonical call-edge snapshots should stay stable across harmless internal id drift"
    );
}

/// A bare closure-surface var id (`αN`, `N = fn_id * 64 + position`) survived
/// into a rendered fact — the drift-prone token this projection dissolves.
fn contains_bare_var_id(snapshot: &str) -> bool {
    let mut chars = snapshot.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == 'α' && chars.peek().is_some_and(|next| next.is_ascii_digit()) {
            return true;
        }
    }
    false
}

#[test]
fn closure_surface_vars_render_by_stable_owner_relative_provenance() {
    // A function that RETURNS a closure exposes the lambda's raw surface arrow
    // in the caller's return type — the one place a closure-surface var reaches
    // a rendered fact instead of being addressed or grounded away. Its id packs
    // `fn_id * 64 + position`, and `fn_id` is a registration-order counter, so
    // the raw `αN` drifts whenever unrelated (e.g. prelude) functions are
    // defined ahead of the lambda. The fact must instead key the var on the
    // lambda's owner-relative source provenance, which is invariant under that
    // churn — stable by construction, no re-bless treadmill.
    let source = r#"
fn add(x) do
  fn y -> x + y end
end

fn main() do
  add(1)
end
"#;
    let snapshot = product_call_edge_snapshot(source);

    // The returned closure's argument and return vars carry owner-relative
    // provenance (`<owner>::lambda[@span]/arity:a{pos}`, `:r`), keyed on the
    // lambda's name/arity + source span + position — never the raw id.
    assert!(
        snapshot.contains("add/1::lambda[@16-33]/1:a0") && snapshot.contains("add/1::lambda[@16-33]/1:r"),
        "closure-surface vars should render by owner-relative provenance + position: {snapshot}"
    );
    assert!(
        !contains_bare_var_id(&snapshot),
        "no closure-surface var should render as a bare drift-prone αN id: {snapshot}"
    );
}

#[test]
fn lowered_callsites_keep_source_span_identity() {
    let source = r#"
fn add1(x), do: x + 1

fn main(), do: add1(41)
"#;
    let tel = ConfiguredTelemetry::new();
    let mut world = crate::compiler2::World::new();
    world.submit_code(Some("fixture.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        "compiler2 should settle the direct-call fixture",
    );

    let main_activation = ActivationKey::from_inputs(root, world.root_function(root), &[], world.types_mut());
    let analysis = world
        .activation_analysis(&main_activation)
        .expect("main activation analysis");
    assert!(
        analysis.callsites.iter().all(|callsite| callsite.span() != Span::DUMMY),
        "user-lowered callsites should preserve their source spans in the data model: {:?}",
        analysis.callsites,
    );
}
