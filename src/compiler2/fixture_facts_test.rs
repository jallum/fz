use super::super::drive_harness::Drive;
use super::super::fixture_facts::{canonical_call_edge_facts, render_canonical_call_edge_snapshot};
use super::super::identity::ActivationKey;
use crate::source::Span;

/// Drives fixture `number` to its backend product and renders its canonical
/// call-edge snapshot over the product-path activation inventory — the same
/// frontier the CLI semantic dump reads. Sourcing the inventory from the
/// product (rather than an ambient fact scan) is what surfaces
/// runtime-demand/callable-flow reached executables such as an escaped lambda
/// passed through an `f.(x)` boundary.
fn product_call_edge_snapshot(number: u32) -> String {
    let mut settled = Drive::fixture(number).settle();
    let root = settled.root();
    let inventory = settled
        .compiler_mut()
        .product_activation_inventory(root)
        .expect("compiler2 should settle the fixture through the product path");
    render_canonical_call_edge_snapshot(&canonical_call_edge_facts(settled.world(), root, &inventory))
}

#[test]
fn canonical_call_edge_facts_preserve_source_spans_and_hide_generated_ids() {
    let mut settled = Drive::fixture(559).settle();
    let root = settled.root();
    let inventory = settled
        .compiler_mut()
        .product_activation_inventory(root)
        .expect("compiler2 should settle the fixture through the product path");

    let facts = canonical_call_edge_facts(settled.world(), root, &inventory);
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
        snapshot.contains("#lambda@"),
        "generated lambdas should still keep stable owner-relative provenance: {snapshot}",
    );
}

#[test]
fn canonical_call_edge_snapshots_are_stable_across_reruns() {
    let first = product_call_edge_snapshot(559);
    let second = product_call_edge_snapshot(559);
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
    let snapshot = product_call_edge_snapshot(560);

    // The returned closure's argument and return vars carry owner-relative
    // provenance, keyed on its typed owner's structural source occurrence,
    // never its source span or raw id.
    assert!(
        snapshot.contains("add/1#lambda@0/1:a0") && snapshot.contains("add/1#lambda@0/1:r"),
        "closure-surface vars should render by owner-relative provenance + position: {snapshot}"
    );
    assert!(
        !contains_bare_var_id(&snapshot),
        "no closure-surface var should render as a bare drift-prone αN id: {snapshot}"
    );
}

#[test]
fn lowered_callsites_keep_source_span_identity() {
    let mut settled = Drive::fixture(561).settle();
    let root = settled.root();
    let world = settled.compiler_mut().world_mut();

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

#[cfg(test)]
mod capture_tag_tests {
    use super::super::{World, drop_closure_capture_tag, stable_type_text};
    use crate::telemetry::ConfiguredTelemetry;

    /// Runs `drop_closure_capture_tag` over `input` and returns what's left
    /// in the iterator afterward, so tests can assert on the untouched tail
    /// (empty when the whole rest of the input was consumed).
    fn strip(input: &str) -> String {
        let mut chars = input.chars().peekable();
        drop_closure_capture_tag(&mut chars);
        chars.collect()
    }

    #[test]
    fn leaves_non_tag_text_untouched() {
        assert_eq!(strip("int"), "int");
    }

    #[test]
    fn leaves_partial_prefix_match_untouched() {
        // `closureXYZ[...]` shares a prefix with the tag but isn't it: the
        // exact literal `closure[` must match, not just `closure`.
        assert_eq!(strip("closureXYZ[atom]"), "closureXYZ[atom]");
    }

    #[test]
    fn strips_a_flat_capture() {
        assert_eq!(strip("closure[int] rest"), " rest");
    }

    #[test]
    fn balances_nested_capture_brackets() {
        // A captured type can itself be a list (e.g. `closure[[int], atom]`),
        // nesting further `[`/`]` pairs inside the tag. A naive "stop at the
        // first `]`" strip would truncate at `closure[[int]` and leave
        // `, atom] rest` dangling.
        let input = "closure[[int], atom] rest";
        assert_eq!(strip(input), " rest");

        // Pin the bite: show what the naive (non-balanced) strip would have
        // produced, and confirm it differs from the correct result above.
        let naive_tag_end = input.find(']').expect("input has a `]`");
        let naive_remainder = &input[naive_tag_end + 1..];
        assert_eq!(naive_remainder, ", atom] rest");
        assert_ne!(naive_remainder, strip(input));
    }

    #[test]
    fn leaves_an_adjacent_unrelated_list_untouched() {
        assert_eq!(strip("closure[int] [str]"), " [str]");
    }

    #[test]
    fn on_unbalanced_input_consumes_to_end_of_string() {
        // `format_closure_lit_suffix` (compiler2::types::format) always emits
        // balanced brackets, so unbalanced input is unreachable from a real
        // render today. This pins the current behavior — consume to
        // end-of-string rather than backing off — rather than leaving it as
        // an untested surprise, so a future refactor changes it on purpose
        // or not at all.
        assert_eq!(strip("closure[int, [int]"), "");
    }

    #[test]
    fn stable_type_text_strips_the_capture_tag_call_edges_carry() {
        // Mirrors the real shape a call-edge snapshot renders: a volatile
        // `#<id>` suffix immediately followed by the closure literal's
        // capture tag, both of which `stable_type_text` treats as noise.
        let _tel = ConfiguredTelemetry::new();
        let world = World::new();
        let rendered = "(a0_p0) -> a0_r#14closure[int, atom] => int".to_string();
        assert_eq!(stable_type_text(&world, rendered), "(a0_p0) -> a0_r => int");
    }
}
