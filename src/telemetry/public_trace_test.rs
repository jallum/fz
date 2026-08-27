use super::*;
use crate::compiler2::DriveOutcome;
use crate::telemetry::handler::EventKind;

/// The ticket's acceptance scenario: two functions, one calling the other.
/// `main/0` is required — `PublicTrace::compile` closes it as the root, the
/// same way `fz2 run`/`interp`/`build` do.
const TWO_FORMULA_SOURCE: &str = "fn helper(x), do: x + 1\nfn main(), do: helper(41)\n";

fn named(ev: &PublicEvent, name: &[&str]) -> bool {
    ev.name.iter().map(String::as_str).eq(name.iter().copied())
}

/// The public trace tells the causal story of a compile: code is indexed,
/// jobs run to close the root, and the root's backend program is defined
/// before the pull session that drove it reports finished. This test proves
/// that story is readable from the *public* stream alone — the same stream
/// `fz2 --log-telemetry` writes in production.
#[test]
fn compile_reports_resolved_and_an_ordered_causal_chain() {
    let trace = PublicTrace::compile(TWO_FORMULA_SOURCE);

    assert!(
        matches!(trace.outcome, DriveOutcome::Resolved),
        "expected the root to resolve, got a different outcome"
    );
    assert!(!trace.events().is_empty(), "public stream must not be empty");

    let first_index = |name: &[&str]| {
        trace
            .events()
            .iter()
            .position(|ev| named(ev, name))
            .unwrap_or_else(|| panic!("expected an event named {name:?} in the public stream"))
    };
    let last_index = |name: &[&str]| {
        trace
            .events()
            .iter()
            .rposition(|ev| named(ev, name))
            .unwrap_or_else(|| panic!("expected an event named {name:?} in the public stream"))
    };

    let first_job_start = trace
        .events()
        .iter()
        .position(|ev| ev.kind == EventKind::SpanStart && named(ev, &["fz", "compiler2", "job"]))
        .expect("expected at least one fz.compiler2.job span_start");
    let first_product_settled = first_index(&["fz", "compiler2", "pull", "product", "settled"]);
    let first_backend_program_defined = first_index(&["fz", "compiler2", "backend_program", "defined"]);
    let last_session_finished = last_index(&["fz", "compiler2", "pull", "session", "finished"]);

    // The causal shape the public stream must preserve: the drive opens a
    // job before it can settle any product, the root's backend program is
    // defined only once the product graph is settled, and the pull session
    // that drove the whole compile reports finished last.
    assert!(
        first_job_start < first_product_settled,
        "a job must start before any product settles"
    );
    assert!(
        first_product_settled < first_backend_program_defined,
        "products must settle before the backend program they compose is defined"
    );
    assert!(
        first_backend_program_defined <= last_session_finished,
        "the backend program must be defined no later than the session that produced it finishing"
    );
}

/// Every `span_start` in the public stream has a matching `span_stop` with
/// the same `span_id`, and every span's parent is either the untraced
/// ambient root (the `fz.compiler2.drive` span itself is not public — it is
/// not in the allowlist) or another span this same stream opened. A trace
/// that failed either property would mean the public projection lost or
/// scrambled structure the production renderer depends on.
#[test]
fn spans_are_paired_and_nesting_only_references_known_spans() {
    let trace = PublicTrace::compile(TWO_FORMULA_SOURCE);
    assert!(matches!(trace.outcome, DriveOutcome::Resolved));

    let spans = trace.spans();
    assert!(!spans.is_empty(), "expected at least one paired span");
    for span in &spans {
        assert!(
            span.stop.is_some(),
            "span_id {} ({:?}) started but never stopped in the public stream",
            span.span_id,
            span.start.name,
        );
    }

    // The ambient root every top-level span nests under: the parent of the
    // very first span this stream opens. It is never itself a `span_id` in
    // this stream because `["fz","compiler2","drive"]` is not public.
    let ambient_root = spans[0].parent_span_id;
    let known_span_ids: std::collections::HashSet<u64> = spans.iter().map(|span| span.span_id).collect();
    assert!(
        !known_span_ids.contains(&ambient_root),
        "the ambient root parent must not itself be a public span (drive is not in the allowlist)"
    );

    for event in trace.events() {
        if event.parent_span_id == 0 {
            continue;
        }
        assert!(
            event.parent_span_id == ambient_root || known_span_ids.contains(&event.parent_span_id),
            "event {:?} has parent_span_id {} that is neither the ambient root ({ambient_root}) nor a known public span",
            event.name,
            event.parent_span_id,
        );
    }
}

/// `fz.compiler2.job` span metadata carries the job's identity (`kind`) on
/// start and its `world`/`completion` outcome on stop — the facts a reader
/// of the public log needs to reconstruct what each job did, without ever
/// touching a raw `Job`/`World`/`JobCompletion` value.
#[test]
fn job_span_metadata_carries_kind_on_start_and_completion_on_stop() {
    let trace = PublicTrace::compile(TWO_FORMULA_SOURCE);
    assert!(matches!(trace.outcome, DriveOutcome::Resolved));

    let job_spans = trace.spans_named(&["fz", "compiler2", "job"]);
    assert!(!job_spans.is_empty(), "expected at least one fz.compiler2.job span");

    for span in &job_spans {
        let job = span
            .start
            .metadata_key("job")
            .unwrap_or_else(|| panic!("job span_start metadata missing \"job\": {:?}", span.start.metadata));
        assert!(
            job.get("kind").and_then(|v| v.as_str()).is_some(),
            "job span_start metadata.job missing string \"kind\": {job:?}"
        );

        let stop = span.stop.as_ref().expect("job span must have a stop");
        assert!(
            stop.metadata_key("completion").is_some(),
            "job span_stop metadata missing \"completion\": {:?}",
            stop.metadata
        );
        assert!(
            stop.metadata_key("world").is_some(),
            "job span_stop metadata missing \"world\": {:?}",
            stop.metadata
        );
        assert!(
            stop.measurements.get("elapsed_ns").and_then(|v| v.as_u64()).is_some(),
            "job span_stop measurements missing numeric \"elapsed_ns\": {:?}",
            stop.measurements
        );
    }
}

/// Guard: proves the helper cannot see anything the production allowlist
/// would filter out. `work_graph.applied` fires unconditionally on every job
/// completion (`drive.rs`) but is never in `is_public_compiler2_trace_event`.
/// A raw `Capture` attached alongside the public writer sees it; the parsed
/// public stream must not. Hand-assembled here (rather than through
/// `PublicTrace::compile`) so the helper's API stays minimal — this is a
/// one-off boundary proof, not a query surface tests need routinely.
#[test]
fn public_stream_excludes_events_the_allowlist_filters_even_when_a_raw_capture_sees_them() {
    let telemetry = crate::telemetry::ConfiguredTelemetry::new();
    let (buf, writer) = crate::telemetry::capture::vec_writer();
    crate::telemetry::JsonlBackend::new_public_writer(writer).install(&telemetry);
    let raw = crate::telemetry::Capture::new();
    raw.install(&telemetry, &[]);

    let outcome = {
        let mut compiler = crate::compiler2::Compiler2::new(telemetry);
        compiler.submit_code(crate::compiler2::CodeSubmission {
            name: Some("public_trace_guard_test.fz".to_string()),
            text: TWO_FORMULA_SOURCE.to_string(),
        });
        compiler.submit_root(crate::compiler2::RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: crate::compiler2::ExecutableNeed::Value,
        });
        compiler.drive()
    };
    assert!(matches!(outcome, DriveOutcome::Resolved));

    assert!(
        raw.contains(&["fz", "compiler2", "work_graph", "applied"]),
        "the raw capture, which bypasses the allowlist, must see work_graph.applied \
         (it fires unconditionally on every job completion)"
    );

    let public = parse_public_trace(&buf.borrow());
    assert!(
        !public.is_empty(),
        "the public stream must still be non-empty — the guard is about what's excluded, not everything"
    );
    assert!(
        public
            .iter()
            .all(|ev| !named(ev, &["fz", "compiler2", "work_graph", "applied"])),
        "the public stream must never contain work_graph.applied — it is not in the production allowlist"
    );
}

/// The buffered public writer only flushes reliably when its backend drops
/// (`JsonlBackend::drop`) — for this two-formula compile the stream is over
/// 64KB, so one auto-flush already fires mid-drive (`jsonl.rs`'s `buffered`
/// threshold), leaving a non-empty but INCOMPLETE prefix sitting in the sink
/// right up until drop. This is exactly the trap fz-kdt.34's own multi-day
/// misdiagnosis fell into: reading "too early" looks like a legitimate,
/// non-empty stream. `PublicTrace::compile` must encapsulate the fix — a
/// caller who never sees the `Compiler2`/`ConfiguredTelemetry` gets the
/// complete post-drop stream, not the pre-drop prefix.
#[test]
fn compile_flushes_the_complete_stream_past_the_pre_drop_auto_flush() {
    let telemetry = crate::telemetry::ConfiguredTelemetry::new();
    let (buf, writer) = crate::telemetry::capture::vec_writer();
    crate::telemetry::JsonlBackend::new_public_writer(writer).install(&telemetry);

    let (outcome, pre_drop_len) = {
        let mut compiler = crate::compiler2::Compiler2::new(telemetry);
        compiler.submit_code(crate::compiler2::CodeSubmission {
            name: Some("public_trace_lifecycle_test.fz".to_string()),
            text: TWO_FORMULA_SOURCE.to_string(),
        });
        compiler.submit_root(crate::compiler2::RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: crate::compiler2::ExecutableNeed::Value,
        });
        let outcome = compiler.drive();
        // Still inside the scope: `compiler` (and with it the telemetry and
        // the backend's last `Rc`) has not dropped yet, so any bytes past
        // the last 64KB auto-flush are still sitting in the backend's
        // internal buffer, not in `buf`.
        (outcome, buf.borrow().len())
    };
    assert!(matches!(outcome, DriveOutcome::Resolved));
    let post_drop_len = buf.borrow().len();

    assert!(
        pre_drop_len > 0,
        "expected the 64KB auto-flush to have already fired at least once mid-drive"
    );
    assert!(
        post_drop_len > pre_drop_len,
        "expected Drop to flush additional bytes past the pre-drop read (pre={pre_drop_len}, post={post_drop_len})"
    );

    let pre_drop_events = parse_public_trace(&buf.borrow()[..pre_drop_len]);
    let post_drop_events = parse_public_trace(&buf.borrow());
    assert!(
        post_drop_events.len() > pre_drop_events.len(),
        "a pre-drop read must observe strictly fewer events than the complete stream"
    );

    // The sanctioned way to get the complete stream never exposes the
    // pre-drop prefix at all.
    let trace = PublicTrace::compile(TWO_FORMULA_SOURCE);
    assert_eq!(
        trace.events().len(),
        post_drop_events.len(),
        "PublicTrace::compile must return exactly the complete, post-drop stream"
    );
    assert!(
        !trace
            .events_named(&["fz", "compiler2", "pull", "session", "finished"])
            .is_empty(),
        "the complete stream must include the pull session finishing, not just the pre-drop prefix"
    );
}

/// fz-kdt.34.2's acceptance scenario: one function, `identity/1`, activated
/// at two different input types (an integer and an atom). Verified to
/// actually produce two `AnalyzeActivation` job spans sharing `function_id`
/// (see `analyze_activation_job_spans_distinguish_two_activations_of_one_function`)
/// before this const was finalized.
const SAME_FUNCTION_TWO_TYPES_SOURCE: &str =
    "fn identity(x), do: x\nfn main() do\n  identity(1)\n  identity(:atom)\nend\n";

/// Before fz-kdt.34.2, `write_opaque` rendered a `Job` as a bare variant
/// name — every `AnalyzeActivation` job span carried only
/// `"kind":"AnalyzeActivation"`, making the 1,382 separate activations a
/// real compile can produce indistinguishable in the public log. This proves
/// the projection now renders within-run identity: two activations of the
/// SAME function (`identity/1`, called once with an int and once with an
/// atom) show equal `function_id` and different `arrow` in the public
/// stream.
#[test]
fn analyze_activation_job_spans_distinguish_two_activations_of_one_function() {
    let trace = PublicTrace::compile(SAME_FUNCTION_TWO_TYPES_SOURCE);
    assert!(matches!(trace.outcome, DriveOutcome::Resolved));

    let job_spans = trace.spans_named(&["fz", "compiler2", "job"]);
    let analyze_activations: Vec<(u64, u64)> = job_spans
        .iter()
        .filter_map(|span| {
            let job = span.start.metadata_key("job")?;
            if job.get("kind").and_then(|v| v.as_str()) != Some("AnalyzeActivation") {
                return None;
            }
            let function_id = job.get("function_id")?.as_u64()?;
            let arrow = job.get("arrow")?.as_u64()?;
            Some((function_id, arrow))
        })
        .collect();

    assert!(
        analyze_activations.len() >= 2,
        "expected at least two AnalyzeActivation job spans with function_id/arrow metadata, got {analyze_activations:?}"
    );

    let mut arrows_by_function: std::collections::HashMap<u64, std::collections::HashSet<u64>> =
        std::collections::HashMap::new();
    for (function_id, arrow) in &analyze_activations {
        arrows_by_function.entry(*function_id).or_default().insert(*arrow);
    }
    assert!(
        arrows_by_function.values().any(|arrows| arrows.len() >= 2),
        "expected two AnalyzeActivation job spans with EQUAL function_id and DIFFERENT arrow \
         (two activations of one function distinguishable in the public log): {analyze_activations:?}"
    );
}

/// A settled `backend_executable` product carries identity beyond `"kind"`:
/// the activation it was built for (`function_id`, `arrow`) and which need
/// it answers (`need`).
#[test]
fn backend_executable_product_settled_carries_identity_beyond_kind() {
    let trace = PublicTrace::compile(SAME_FUNCTION_TWO_TYPES_SOURCE);
    assert!(matches!(trace.outcome, DriveOutcome::Resolved));

    let settled = trace.events_named(&["fz", "compiler2", "pull", "product", "settled"]);
    let backend_executable = settled
        .iter()
        .filter_map(|ev| ev.metadata_key("product"))
        .find(|product| product.get("kind").and_then(|v| v.as_str()) == Some("backend_executable"))
        .unwrap_or_else(|| panic!("expected a settled backend_executable product in {settled:?}"));

    assert!(
        backend_executable.get("function_id").and_then(|v| v.as_u64()).is_some(),
        "backend_executable product metadata missing function_id: {backend_executable:?}"
    );
    assert!(
        backend_executable.get("arrow").and_then(|v| v.as_u64()).is_some(),
        "backend_executable product metadata missing arrow: {backend_executable:?}"
    );
    assert!(
        backend_executable.get("need").and_then(|v| v.as_str()).is_some(),
        "backend_executable product metadata missing need: {backend_executable:?}"
    );
}
