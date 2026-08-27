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

/// The identity portion of a `work_graph.applied` completion object — its
/// `"kind"` plus id fields — with the non-identity fields (`opaque_type`,
/// `rebased`, and the applied-step batches) stripped out. Lets a test
/// compare "this job" (as `wakes[].job` renders it) against "this
/// completion" (as the top-level `JobCompletion` opaque body renders it)
/// even though the two renderers include a different set of surrounding
/// keys.
fn completion_job_identity(completion: &serde_json::Value) -> serde_json::Value {
    fact_identity(
        completion,
        &["opaque_type", "rebased", "changed", "wakes", "movements", "blocked"],
    )
}

/// `value` with `exclude` keys stripped, for comparing two differently
/// shaped renderings of "the same identity" (a `FactChange`'s `"kind"` +
/// ids vs. a `FactUse`'s `"use"` + `"kind"` + ids, or a `JobCompletion`'s
/// `"kind"` + ids vs. a `Wake`'s `job` object).
fn fact_identity(value: &serde_json::Value, exclude: &[&str]) -> serde_json::Value {
    let object = value
        .as_object()
        .unwrap_or_else(|| panic!("expected a JSON object, got {value:?}"));
    let mut identity = serde_json::Map::new();
    for (key, v) in object {
        if exclude.contains(&key.as_str()) {
            continue;
        }
        identity.insert(key.clone(), v.clone());
    }
    serde_json::Value::Object(identity)
}

/// fz-kdt.34.3's acceptance scenario: the causal chain a `work_graph.applied`
/// completion carries — cause fact -> attributed wake -> the woken job's own
/// later evaluation — must be readable end to end from the *public* log
/// alone, the same stream `fz2 --log-telemetry` writes in production.
///
/// This picks the first `IndexCode` completion that woke something (a
/// stable early link: `IndexCode` is always among the first jobs to run and
/// its `CodeIndexed` output always has a subscriber), and proves three
/// things hold together: the wake's `cause` is genuinely one of *this*
/// completion's own `changed` facts (not asserted in a vacuum), the
/// disposition is the woken job's real work start, and a later
/// `work_graph.applied` event exists for exactly that woken job — i.e. the
/// public log lets a reader walk cause -> wake -> evaluation in order.
#[test]
fn work_graph_applied_carries_a_readable_cause_wake_evaluation_chain() {
    let trace = PublicTrace::compile(TWO_FORMULA_SOURCE);
    assert!(matches!(trace.outcome, DriveOutcome::Resolved));

    let applied = trace.events_named(&["fz", "compiler2", "work_graph", "applied"]);
    assert!(!applied.is_empty(), "expected at least one work_graph.applied event");

    let (cause_index, cause_completion, wake) = applied
        .iter()
        .enumerate()
        .find_map(|(index, ev)| {
            let completion = ev.metadata_key("completion")?;
            if completion.get("kind").and_then(|v| v.as_str()) != Some("IndexCode") {
                return None;
            }
            let wake = completion.get("wakes")?.as_array()?.first()?.clone();
            Some((index, completion, wake))
        })
        .unwrap_or_else(|| panic!("expected an IndexCode work_graph.applied event with at least one wake"));

    // The cause is not asserted in a vacuum: it must be one of this same
    // completion's own changed facts.
    let cause = wake.get("cause").expect("wake missing \"cause\"");
    let changed = cause_completion
        .get("changed")
        .and_then(|v| v.as_array())
        .expect("completion missing \"changed\" array");
    let cause_identity = fact_identity(cause, &["use"]);
    assert!(
        changed.iter().any(|change| fact_identity(
            change,
            &["old_revision", "new_revision", "old_settled", "new_settled"]
        ) == cause_identity),
        "the wake's cause {cause:?} must be one of this completion's own changed facts: {changed:?}"
    );

    assert_eq!(
        wake.get("disposition").and_then(|v| v.as_str()),
        Some("enqueued"),
        "the first wake a fresh job receives should be its real work start: {wake:?}"
    );

    // The chain closes: the woken job must itself later report its own
    // work_graph.applied completion, after the event that caused it.
    let woken_job = wake.get("job").expect("wake missing \"job\"");
    let evaluation = applied.iter().enumerate().skip(cause_index + 1).find(|(_, ev)| {
        let completion = ev
            .metadata_key("completion")
            .expect("work_graph.applied event missing \"completion\"");
        &completion_job_identity(completion) == woken_job
    });
    assert!(
        evaluation.is_some(),
        "expected a later work_graph.applied event for the woken job {woken_job:?} \
         (the event that caused it is at index {cause_index} of {} applied events)",
        applied.len()
    );
}

/// Guard: proves the helper cannot see anything the production allowlist
/// would filter out. `["fz","compiler2","function","defined"]` fires
/// unconditionally on every function definition (`World::define_function`,
/// via `emit_world_key`) but is never in `is_public_compiler2_trace_event`.
/// A raw `Capture` attached alongside the public writer sees it; the parsed
/// public stream must not. Hand-assembled here (rather than through
/// `PublicTrace::compile`) so the helper's API stays minimal — this is a
/// one-off boundary proof, not a query surface tests need routinely.
///
/// `work_graph.applied` used to be this test's witness — before fz-kdt.34.3
/// it fired unconditionally on every job completion but was excluded from
/// the allowlist the same way. fz-kdt.34.3 makes it public, so a witness
/// that stays excluded had to move; this test now also asserts the positive
/// side of that change — the public stream DOES carry `work_graph.applied`.
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
        raw.contains(&["fz", "compiler2", "function", "defined"]),
        "the raw capture, which bypasses the allowlist, must see function.defined \
         (it fires unconditionally on every function definition)"
    );

    let public = parse_public_trace(&buf.borrow());
    assert!(
        !public.is_empty(),
        "the public stream must still be non-empty — the guard is about what's excluded, not everything"
    );
    assert!(
        public
            .iter()
            .all(|ev| !named(ev, &["fz", "compiler2", "function", "defined"])),
        "the public stream must never contain function.defined — it is not in the production allowlist"
    );
    assert!(
        public
            .iter()
            .any(|ev| named(ev, &["fz", "compiler2", "work_graph", "applied"])),
        "work_graph.applied is public as of fz-kdt.34.3 — the allowlist change must be observable"
    );
}

/// The buffered public writer only flushes reliably when its backend drops
/// (`JsonlBackend::drop`). This is exactly the trap fz-kdt.34's own
/// multi-day misdiagnosis fell into: reading "too early" can look like a
/// legitimate stream. `PublicTrace::compile` must encapsulate the fix — a
/// caller who never sees the `Compiler2`/`ConfiguredTelemetry` gets the
/// complete post-drop stream, not the pre-drop prefix.
///
/// Two sub-proofs, at two different auto-flush thresholds:
///
/// (1) at the PRODUCTION 64KB threshold, this two-formula compile's stream
/// is well over 64KB, so at least one auto-flush has already fired by the
/// time `drive()` returns — `pre_drop_len > 0` on its own is enough to show
/// that (whether the very last bytes also happen to land exactly on a flush
/// boundary is incidental to total byte volume, not something this proof
/// depends on: fz-kdt.34.4 alone changed that volume by closing the product
/// settlement undercount, precisely the kind of legitimate future volume
/// change this sub-proof must stay robust to).
///
/// (2) at a threshold deliberately set past the whole stream's length
/// (`usize::MAX`), NOTHING auto-flushes mid-drive by construction — every
/// byte is still sitting in the backend's internal buffer when `drive()`
/// returns, so `pre_drop_len` is deterministically `0` and `post_drop_len`
/// (Drop's unconditional final flush) is deterministically the complete
/// stream. This is the same "Drop must flush what's buffered" invariant as
/// (1), proven without depending on any incidental byte-count alignment at
/// all.
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
        post_drop_len >= pre_drop_len,
        "Drop's flush must never lose bytes the mid-drive auto-flush already wrote \
         (pre={pre_drop_len}, post={post_drop_len})"
    );

    // Sub-proof (2): an unreachable auto-flush threshold, so Drop is
    // observably the ONLY thing that ever moves bytes into the sink.
    let telemetry = crate::telemetry::ConfiguredTelemetry::new();
    let (unflushed_buf, unflushed_writer) = crate::telemetry::capture::vec_writer();
    crate::telemetry::JsonlBackend::new_public_writer_with_threshold(unflushed_writer, usize::MAX).install(&telemetry);

    let (outcome, pre_drop_len_unflushed) = {
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
        (outcome, unflushed_buf.borrow().len())
    };
    assert!(matches!(outcome, DriveOutcome::Resolved));
    let post_drop_len_unflushed = unflushed_buf.borrow().len();

    assert_eq!(
        pre_drop_len_unflushed, 0,
        "an unreachable auto-flush threshold must leave the sink untouched until drop"
    );
    assert!(
        post_drop_len_unflushed > 0,
        "Drop must flush the complete buffered stream even when no auto-flush ever fired"
    );

    let pre_drop_events = parse_public_trace(&unflushed_buf.borrow()[..pre_drop_len_unflushed]);
    let post_drop_events = parse_public_trace(&unflushed_buf.borrow());
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

/// fz-kdt.34.4: before this ticket, `pull.product.settled` fired at most
/// once per `ProductDriver::pull` call -- an anchor-only event with no
/// generation/changed/group at all -- so a settled GROUP's co-published
/// members (every member besides the one the driver happened to pull, e.g.
/// a callable-construction SCC or a demand cone) settled INVISIBLY. This
/// proves, against the real public stream a production compile writes, that
/// the undercount is closed: (a) is the handler-fires proof from the arity
/// trap in the ticket -- it can only pass if the new arity-3
/// `attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>`
/// handler in `jsonl.rs` actually fired and `write_opaque`'s new
/// `ProductSettlement` arm actually rendered; (b) proves the group
/// co-publication path specifically, by requiring more than one distinct
/// `transport_shape` product key among the settled rows -- probed and
/// confirmed stable: on this fixture `runtime_demand` collapses to a single
/// executable (the two `identity` activations fully resolve into one
/// backend executable, so its demand cone never grows a second member),
/// while `transport_shape` -- settled through the exact same
/// `ProductMemo::finish_group` authority a demand cone's co-publication
/// used to bypass -- reliably produces over a dozen distinct member keys
/// even on this small a program; (c) proves the newly-public
/// `cache_hit`/`reentered`/`displaced` events ride the existing
/// `["fz","compiler2","pull","product"]` prefix projection without a code
/// change, and that adding `pull.product.settled`'s new arity did not
/// silently disable that sibling arity-1 registration on the same prefix
/// (the exact trap this ticket calls out).
#[test]
fn public_settled_events_carry_settlement_and_multiple_transport_shape_products_settle_with_a_cache_hit() {
    let trace = PublicTrace::compile(SAME_FUNCTION_TWO_TYPES_SOURCE);
    assert!(matches!(trace.outcome, DriveOutcome::Resolved));

    let settled = trace.events_named(&["fz", "compiler2", "pull", "product", "settled"]);
    assert!(
        !settled.is_empty(),
        "expected at least one settled product in the public stream"
    );

    // (a) THE PROOF the arity-3 settled handler fires and renders: every
    // public settled row carries a `settlement` object with generation >= 1.
    for ev in &settled {
        let settlement = ev
            .metadata_key("settlement")
            .unwrap_or_else(|| panic!("settled event missing settlement metadata: {ev:?}"));
        let generation = settlement
            .get("generation")
            .and_then(|v| v.as_u64())
            .unwrap_or_else(|| panic!("settlement missing generation: {settlement:?}"));
        assert!(generation >= 1, "settlement generation must be >= 1, got {generation}");
        assert!(
            settlement.get("changed").and_then(|v| v.as_bool()).is_some(),
            "settlement missing changed: {settlement:?}"
        );
        assert!(
            settlement.get("group").is_some(),
            "settlement missing group (should be present, null when not a group member): {settlement:?}"
        );
    }

    // (b) the previously-silent group co-publication path: more than one
    // distinct settled `transport_shape` product key appears.
    let transport_shape_keys: std::collections::HashSet<String> = settled
        .iter()
        .filter_map(|ev| ev.metadata_key("product"))
        .filter(|product| product.get("kind").and_then(|v| v.as_str()) == Some("transport_shape"))
        .map(|product| product.to_string())
        .collect();
    assert!(
        transport_shape_keys.len() > 1,
        "expected more than one distinct settled transport_shape product key \
         (a settled group's co-published members), got {transport_shape_keys:?}"
    );

    // (c) the allowlist addition is observable: cache_hit is public.
    let cache_hits = trace.events_named(&["fz", "compiler2", "pull", "product", "cache_hit"]);
    assert!(!cache_hits.is_empty(), "expected at least one public cache_hit event");
}

/// fz-kdt.34.5: `demand_on_stall`'s aggregate tally (`pull.session.finished`'s
/// `work_starts_blocked_waiter_expansion`) says how many work starts were a
/// blocked-waiter expansion, but never which fact drove any one of them.
/// This test pins the whole chain from the public log alone, for
/// `TWO_FORMULA_SOURCE`'s deterministic first stall: `main/0` (function id
/// 0, the root's own entry function) is submitted before its `FunctionDefined`
/// fact exists, so the root's `SeedRoot` blocks on it and the very first
/// stall pass demands its producer.
///
/// (a) `demand_on_stall` is public at all (today it is not in the
/// allowlist, so this alone is the red assertion), with at least one
/// producer poked; (b) its `demanded_facts.facts` array names the exact
/// fact — `{"kind":"FunctionDefined","function_id":0}` — with
/// `"reason":"blocked_waiter_expansion"`; (c) the chain closes: a later
/// `work_graph.applied` event's `completion` is `DefineFunction(0)`, the
/// job `World::demand_fact_producer` maps `FunctionDefined` to
/// (drive.rs's fact->producer map).
#[test]
fn demand_on_stall_names_the_exact_fact_and_closes_to_its_producer() {
    let trace = PublicTrace::compile(TWO_FORMULA_SOURCE);
    assert!(matches!(trace.outcome, DriveOutcome::Resolved));

    let events = trace.events();
    let (stall_index, stall_event) = events
        .iter()
        .enumerate()
        .find(|(_, ev)| named(ev, &["fz", "compiler2", "drive", "demand_on_stall"]))
        .unwrap_or_else(|| panic!("expected a public fz.compiler2.drive.demand_on_stall event"));

    // (a) present, with a real producer poke.
    let producer_pokes = stall_event
        .metadata_key("producer_pokes")
        .and_then(|v| v.as_u64())
        .unwrap_or_else(|| panic!("demand_on_stall missing producer_pokes: {stall_event:?}"));
    assert!(
        producer_pokes >= 1,
        "expected demand_on_stall's producer_pokes >= 1, got {producer_pokes}"
    );

    // (b) the exact demanded fact, and the uniform reason.
    let demanded_facts = stall_event
        .metadata_key("demanded_facts")
        .unwrap_or_else(|| panic!("demand_on_stall missing demanded_facts: {stall_event:?}"));
    let facts = demanded_facts
        .get("facts")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("demanded_facts missing a facts array: {demanded_facts:?}"));
    let pinned_fact = serde_json::json!({"kind": "FunctionDefined", "function_id": 0});
    assert!(
        facts.contains(&pinned_fact),
        "expected demand_on_stall's demanded_facts.facts to contain {pinned_fact}, got {facts:?}"
    );
    assert_eq!(
        stall_event.metadata_key("reason").and_then(|v| v.as_str()),
        Some("blocked_waiter_expansion"),
        "expected demand_on_stall's reason to be blocked_waiter_expansion, got {:?}",
        stall_event.metadata_key("reason")
    );

    // (c) the chain closes: the fact->producer map sends `FunctionDefined(0)`
    // to `Job::DefineFunction(0)` — a later public work_graph.applied event
    // must run exactly that job.
    let closes_to_producer = events[stall_index + 1..].iter().any(|ev| {
        named(ev, &["fz", "compiler2", "work_graph", "applied"])
            && ev.metadata_key("completion").is_some_and(|completion| {
                completion.get("kind").and_then(|v| v.as_str()) == Some("DefineFunction")
                    && completion.get("function_id").and_then(|v| v.as_u64()) == Some(0)
            })
    });
    assert!(
        closes_to_producer,
        "expected a work_graph.applied event after the stall pass running DefineFunction(0), \
         the producer FunctionDefined(0) maps to"
    );
}
