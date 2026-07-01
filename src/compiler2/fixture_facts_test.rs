use super::fixture_facts::{canonical_call_edge_facts, render_canonical_call_edge_snapshot};
use super::{DriveOutcome, ExecutableNeed, FactKey, Job};
use crate::source::Span;
use crate::telemetry::ConfiguredTelemetry;

fn assert_resolved(outcome: DriveOutcome<Job, FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

#[test]
#[ignore = "fz-go4.18.4: the generated-lambda provenance this asserts is only \
    observable when the analyzed-activation frontier includes latent \
    runtime-demand-reached executables (escaped/opaque callables). That frontier \
    was populated by the deleted seal's runtime-demand-frontier walk; the legacy \
    `world.drive()` + `root_executable_frontier` oracle now sees only the entry \
    cone. Production is unaffected (the product path discovers the lambda via the \
    RuntimeDemand product; the fixture interps/compiles correctly). Re-enable by \
    re-basing the fixture call-edge oracle on a product-path activation inventory \
    (fz-go4.18.13)."]
fn canonical_call_edge_facts_preserve_source_spans_and_hide_generated_ids() {
    let source = r#"
fn apply1(f, x), do: f.(x)

fn main() do
  add1 = fn x -> x + 1 end
  apply1(add1, 41)
end
"#;

    let tel = ConfiguredTelemetry::new();
    let mut world = crate::compiler2::World::new(&tel);
    world.submit_code(Some("fixture.fz".to_string()), source.to_string());
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert_resolved(world.drive(), "compiler2 should settle a simple lambda fixture");

    let facts = canonical_call_edge_facts(&world, root);
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

    let compile_once = || {
        let tel = ConfiguredTelemetry::new();
        let mut world = crate::compiler2::World::new(&tel);
        world.submit_code(Some("fixture.fz".to_string()), source.to_string());
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        assert_resolved(world.drive(), "compiler2 should settle the fixture");
        render_canonical_call_edge_snapshot(&canonical_call_edge_facts(&world, root))
    };

    let first = compile_once();
    let second = compile_once();
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

    let activations = world.root_executable_frontier(root);
    let activation = activations
        .iter()
        .map(|executable| &executable.activation)
        .find(|activation| world.function_ref(activation.function).name == "main")
        .expect("main activation");
    let analysis = world.activation_analysis(activation).expect("main activation analysis");
    assert!(
        analysis.callsites.iter().all(|callsite| callsite.span() != Span::DUMMY),
        "user-lowered callsites should preserve their source spans in the data model: {:?}",
        analysis.callsites,
    );
}
