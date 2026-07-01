use super::fixture_facts::{canonical_call_edge_facts, render_canonical_call_edge_snapshot};
use super::identity::ActivationKey;
use super::{CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, FactKey, Job, RootId, RootSubmission};
use crate::source::Span;
use crate::telemetry::ConfiguredTelemetry;

fn assert_resolved(outcome: DriveOutcome<Job, FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

/// Drives a fixture to its backend product and renders its canonical
/// call-edge snapshot over the product-path activation inventory — the same
/// frontier the CLI semantic dump reads. Sourcing the inventory from the
/// product (rather than an ambient fact scan) is what surfaces
/// runtime-demand/callable-flow reached executables such as an escaped lambda
/// passed through an `f.(x)` boundary.
fn product_call_edge_snapshot(source: &str) -> String {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    let root = build_lambda_root(&mut compiler, source);
    let inventory = compiler
        .product_activation_inventory(root)
        .expect("compiler2 should settle a simple lambda fixture through the product path");
    render_canonical_call_edge_snapshot(&canonical_call_edge_facts(compiler.world(), root, &inventory))
}

fn build_lambda_root(compiler: &mut Compiler2<'_>, source: &str) -> RootId {
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
    let mut compiler = Compiler2::new(&tel);
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

#[test]
fn lowered_callsites_keep_source_span_identity() {
    let source = r#"
fn add1(x), do: x + 1

fn main(), do: add1(41)
"#;
    let tel = ConfiguredTelemetry::new();
    let mut world = crate::compiler2::World::new(&tel);
    world.submit_code(Some("fixture.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive(), "compiler2 should settle the direct-call fixture");

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
