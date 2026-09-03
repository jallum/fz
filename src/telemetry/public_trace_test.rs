use super::*;
use crate::compiler2::DriveOutcome;
use crate::telemetry::causal::{
    CausalReport, FactLifecycle, FormulaWork, ProductEvaluationCause, ProductEvaluationTriggerKind,
    ProductPublicationKind, PublicEvent, ShiftWork,
};
use crate::telemetry::handler::EventKind;

/// The ticket's acceptance scenario: two functions, one calling the other.
/// `main/0` is required — `PublicTrace::compile` closes it as the root, the
/// same way `fz2 run`/`interp`/`build` do.
const TWO_FORMULA_SOURCE: &str = "fn helper(x), do: x + 1\nfn main(), do: helper(41)\n";

fn causal_event(name: &[&str], metadata: serde_json::Value) -> PublicEvent {
    PublicEvent {
        name: name.iter().map(|part| (*part).to_string()).collect(),
        kind: EventKind::Event,
        span_id: 0,
        parent_span_id: 0,
        measurements: serde_json::json!({}),
        metadata,
        semantic: serde_json::json!({}),
    }
}

#[derive(Default)]
struct ReplayEvents(Vec<PublicEvent>);

impl ReplayEvents {
    fn push(&mut self, suffix: &[&str], metadata: serde_json::Value) {
        let mut name = vec!["fz", "compiler2"];
        name.extend_from_slice(suffix);
        self.0.push(causal_event(&name, metadata));
    }

    fn session(&mut self, event: &str, id: u64) {
        self.push(
            &["pull", "session", event],
            serde_json::json!({"session_id": id, "session": {}}),
        );
    }

    fn request(&mut self, product: &serde_json::Value) -> u64 {
        let request_id = self.0.len() as u64 + 1;
        self.push(
            &["pull", "product", "requested"],
            serde_json::json!({"product": product, "request_id": request_id}),
        );
        request_id
    }

    fn evaluate(&mut self, product: &serde_json::Value, waits: &[serde_json::Value]) {
        let request_id = self
            .0
            .iter()
            .rev()
            .find(|event| {
                event.name == ["fz", "compiler2", "pull", "product", "requested"].map(str::to_string)
                    && event.metadata.get("product") == Some(product)
            })
            .and_then(|event| event.metadata.get("request_id"))
            .and_then(serde_json::Value::as_u64)
            .expect("a product evaluation needs its exact request");
        self.push(
            &["pull", "product", "evaluated"],
            serde_json::json!({
                "product": product,
                "request_id": request_id,
                "outcome": {"status": "produced", "waits": waits},
            }),
        );
    }

    fn product_event(&mut self, event: &str, product: &serde_json::Value) {
        self.push(&["pull", "product", event], serde_json::json!({"product": product}));
    }

    fn settle(&mut self, product: &serde_json::Value, generation: u64, changed: bool) {
        self.push(
            &["pull", "product", "settled"],
            serde_json::json!({"product": product, "settlement": {"generation": generation, "changed": changed}}),
        );
    }

    fn backend(&mut self, event: &str, metadata: serde_json::Value) {
        let mut request = serde_json::Map::new();
        request.insert(
            "status".to_string(),
            serde_json::Value::String(if event == "started" { "started" } else { "success" }.to_string()),
        );
        if let Some(program) = metadata.get("program").and_then(serde_json::Value::as_object) {
            request.extend(program.clone());
        }
        self.push(&["backend_request", event], serde_json::json!({"request": request}));
    }

    fn applied(&mut self, completion: serde_json::Value) {
        self.push(
            &["work_graph", "applied"],
            serde_json::json!({"completion": completion}),
        );
    }

    fn movement(&mut self, job: u64, fact: &serde_json::Value) {
        self.applied(serde_json::json!({
            "kind": "SyntheticJob",
            "root_id": job,
            "movements": [{
                "kind": fact["kind"],
                "root_id": fact["root_id"],
                "old_revision": 1,
                "new_revision": 2,
            }],
        }));
    }

    fn recursive_search(&mut self, product: &serde_json::Value, dependency: &serde_json::Value) {
        self.push(
            &["pull", "recursive_group", "searched"],
            serde_json::json!({
                "product": product,
                "dependency": dependency,
                "search": {
                    "candidate_inventory": 2,
                    "vertex_visits": 3,
                    "edge_scans": 2,
                    "cycle_closed": true,
                    "group_members": 2,
                }
            }),
        );
    }
}

#[test]
fn nested_product_session_restores_outer_exact_evaluation_history() {
    let product = |root_id| serde_json::json!({"kind": "root_backend_product", "root_id": root_id});
    let (outer, dependency, inner) = (product(1), product(2), product(3));
    let mut events = ReplayEvents::default();
    events.session("started", 1);
    events.request(&outer);
    events.evaluate(&outer, &[serde_json::json!({"product": dependency})]);
    events.session("started", 2);
    events.request(&inner);
    events.evaluate(&inner, &[]);
    events.session("finished", 2);
    events.settle(&dependency, 1, true);
    events.request(&outer);
    events.evaluate(&outer, &[]);
    events.session("finished", 1);
    let report = CausalReport::derive(&events.0);
    let resumed = report.product_evaluations.last().expect("outer evaluation resumed");
    assert_eq!(resumed.session, 1);
    assert_eq!(resumed.prior_evaluation, Some(2));
    assert_eq!(resumed.cause, ProductEvaluationCause::ProductMovement);
    assert_eq!(resumed.triggers.len(), 1);
    assert_eq!(resumed.triggers[0].position, 7);
    assert_eq!(
        resumed.triggers[0].kind,
        ProductEvaluationTriggerKind::ProductSettlement
    );
}

#[test]
fn failed_backend_request_is_a_balanced_public_lifecycle() {
    let telemetry = ConfiguredTelemetry::new();
    let (buf, writer) = vec_writer();
    JsonlBackend::new_public_writer(writer).install(&telemetry);
    {
        let mut compiler = Compiler2::new(telemetry);
        compiler.submit_code(CodeSubmission {
            name: Some("failed_backend_request.fz".to_string()),
            text: "fn main(), do: 0\n".to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        compiler.set_drive_timeout(std::time::Duration::ZERO);
        assert!(compiler.run_root_interp(root).is_err());
    }

    let events = parse_public_trace(&buf.borrow());
    let lifecycle = events
        .iter()
        .filter(|event| {
            event
                .name
                .starts_with(&["fz".to_string(), "compiler2".to_string(), "backend_request".to_string()])
        })
        .collect::<Vec<_>>();
    assert_eq!(lifecycle.len(), 2, "a failure must retain both request boundaries");
    assert_eq!(
        lifecycle[0].name,
        ["fz", "compiler2", "backend_request", "started"].map(str::to_string)
    );
    assert_eq!(
        lifecycle[1].name,
        ["fz", "compiler2", "backend_request", "finished"].map(str::to_string)
    );
    assert_eq!(lifecycle[0].metadata["request"]["status"], "started");
    assert_eq!(lifecycle[1].metadata["request"]["status"], "failure");
}

#[test]
fn retained_session_classifies_hits_and_equal_reproduction_from_event_order() {
    let product = serde_json::json!({"kind": "root_backend_product", "root_id": 1});
    let mut events = ReplayEvents::default();
    events.session("started", 1);
    events.backend("started", serde_json::json!({}));
    events.request(&product);
    events.evaluate(&product, &[serde_json::json!({"product": product})]);
    events.settle(&product, 1, true);
    events.backend("finished", serde_json::json!({}));
    events.backend("started", serde_json::json!({}));
    events.product_event("cache_hit", &product);
    events.request(&product);
    events.settle(&product, 7, false);
    events.product_event("cache_hit", &product);
    events.evaluate(&product, &[]);
    events.backend("finished", serde_json::json!({}));
    events.session("finished", 1);

    let reports = CausalReport::derive_requests(&events.0);
    assert_eq!(reports.len(), 2);
    let retained = reports[1].product_totals();
    assert_eq!(retained.cache_hits, 2);
    assert_eq!(
        retained.retained_cache_hits, 1,
        "only the hit before this request settles the key is retained"
    );
    assert_eq!(retained.equal_reproductions, 1);
    assert_eq!(retained.first_productions, 0);
    assert_eq!(retained.reproductions, 0);
    let evaluation = reports[1]
        .product_evaluations
        .last()
        .expect("retained-session evaluation");
    assert_eq!(evaluation.session, 1);
    assert_eq!(evaluation.prior_evaluation, Some(3));
    assert_eq!(evaluation.cause, ProductEvaluationCause::ProductMovement);
}

#[test]
fn product_replay_classifies_exact_movements_and_recursive_searches() {
    let product = |id| serde_json::json!({"kind": "synthetic", "root_id": id});
    let fact = |id| serde_json::json!({"kind": "SyntheticFact", "root_id": id, "use": "settled"});
    let fact_owner = product(1);
    let dependency_owner = product(2);
    let self_owner = product(3);
    let mixed_owner = product(4);
    let unrelated_owner = product(5);
    let dependency = product(20);
    let unrelated = product(21);
    let unrelated_wait = product(22);
    let moved_fact = fact(30);
    let mixed_fact = fact(31);
    let mut events = ReplayEvents::default();
    events.session("started", 1);
    {
        let mut initial = |owner: &serde_json::Value, waits: &[serde_json::Value]| {
            events.request(owner);
            events.evaluate(owner, waits);
        };
        initial(&fact_owner, &[serde_json::json!({"fact": moved_fact})]);
        initial(&dependency_owner, &[serde_json::json!({"product": dependency})]);
        initial(&self_owner, &[]);
        initial(
            &mixed_owner,
            &[
                serde_json::json!({"fact": mixed_fact}),
                serde_json::json!({"product": dependency}),
            ],
        );
        initial(&unrelated_owner, &[serde_json::json!({"product": unrelated_wait})]);
    }

    events.movement(40, &moved_fact);
    events.request(&fact_owner);
    events.evaluate(&fact_owner, &[]);
    events.product_event("displaced", &dependency);
    events.request(&dependency_owner);
    events.evaluate(&dependency_owner, &[]);
    events.product_event("displaced", &self_owner);
    events.request(&self_owner);
    events.evaluate(&self_owner, &[]);
    events.movement(41, &mixed_fact);
    events.product_event("displaced", &dependency);
    events.request(&mixed_owner);
    events.recursive_search(&mixed_owner, &dependency);
    events.evaluate(&mixed_owner, &[]);
    events.product_event("displaced", &unrelated);
    events.request(&unrelated_owner);
    events.evaluate(&unrelated_owner, &[]);
    events.session("finished", 1);

    let report = CausalReport::derive(&events.0);
    let causes = report
        .product_evaluations
        .iter()
        .filter(|evaluation| evaluation.prior_evaluation.is_some())
        .map(|evaluation| evaluation.cause)
        .collect::<Vec<_>>();
    assert_eq!(
        causes,
        vec![
            ProductEvaluationCause::FactMovement,
            ProductEvaluationCause::ProductMovement,
            ProductEvaluationCause::Displacement,
            ProductEvaluationCause::Mixed,
            ProductEvaluationCause::Unexplained,
        ]
    );
    let search = report.recursive_searches.first().expect("exact recursive search");
    assert_eq!(search.product.raw, mixed_owner);
    assert_eq!(search.dependency.raw, dependency);
    assert_eq!(search.cause, Some(ProductEvaluationCause::Mixed));
    assert_eq!(
        search.work,
        crate::telemetry::causal::RecursiveSearchWork {
            searches: 1,
            candidate_inventory: 2,
            vertex_visits: 3,
            edge_scans: 2,
            closed_cycles: 1,
            group_members: 2,
        }
    );
}

#[test]
fn request_population_survives_a_cache_only_request() {
    let mut events = ReplayEvents::default();
    events.backend("started", serde_json::json!({}));
    events.backend(
        "finished",
        serde_json::json!({"program": {"executables": 7, "construction_wrappers": 2}}),
    );

    let reports = CausalReport::derive_requests(&events.0);
    assert_eq!(reports.len(), 1);
    assert_eq!(reports[0].final_population.reachable_executables, 7);
    assert_eq!(reports[0].final_population.construction_wrappers, 2);
    assert_eq!(reports[0].product_totals().settlements, 0);
}

#[test]
fn request_reports_count_distinct_moved_facts_per_request() {
    let mut events = ReplayEvents::default();
    for _ in 0..2 {
        events.backend("started", serde_json::json!({}));
        events.applied(serde_json::json!({
            "kind": "SyntheticJob",
            "root_id": 1,
            "changed": [{
                "kind": "SyntheticFact",
                "root_id": 2,
                "old_revision": 1,
                "new_revision": 2,
            }]
        }));
        events.backend("finished", serde_json::json!({"program": {}}));
    }

    let reports = CausalReport::derive_requests(&events.0);
    assert_eq!(reports.len(), 2);
    assert_eq!(reports[0].lifecycles["SyntheticFact"].distinct, 1);
    assert_eq!(reports[1].lifecycles["SyntheticFact"].distinct, 1);
}

#[test]
fn raw_product_rows_remain_distinct_while_canonical_multisets_fold_them() {
    let mut events = ReplayEvents::default();
    for id in 1..=2 {
        events.push(&["canon", "type"], serde_json::json!({"type_id": id, "canon": "int"}));
    }
    events.session("started", 1);
    for arrow in 1..=2 {
        events.request(&serde_json::json!({"kind": "transport_shape", "arrow": arrow}));
    }
    events.session("finished", 1);
    let report = CausalReport::derive(&events.0);
    assert_eq!(report.products.len(), 2, "raw arena identities must not collapse");
    let requests = report
        .canonical_multiset()
        .into_iter()
        .filter(|(key, _)| key.ends_with("\u{1}requests"))
        .collect::<Vec<_>>();
    assert_eq!(requests.len(), 1, "canonical packaging folds equivalent raw keys");
    assert_eq!(requests[0].1, 2);
}

#[test]
fn canonical_product_causality_preserves_fact_use_mode() {
    let report = |fact_use| {
        let product = serde_json::json!({"kind": "synthetic", "root_id": 1});
        let mut events = ReplayEvents::default();
        events.session("started", 1);
        events.request(&product);
        events.evaluate(
            &product,
            &[serde_json::json!({"fact": {
                "use": fact_use,
                "kind": "SyntheticFact",
                "root_id": 2,
            }})],
        );
        events.request(&product);
        events.evaluate(&product, &[]);
        events.session("finished", 1);
        CausalReport::derive(&events.0).canonical_multiset()
    };

    let current = report("current");
    let settled = report("settled");
    let settled_presence = report("settled_presence");
    assert_ne!(current, settled);
    assert_ne!(current, settled_presence);
    assert_ne!(settled, settled_presence);
}

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
/// `cache_hit`/`displaced` events ride the existing
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
    for leaf in ["settled", "displaced", "cache_hit"] {
        for event in trace.events_named(&["fz", "compiler2", "pull", "product", leaf]) {
            let product = event
                .metadata_key("product")
                .unwrap_or_else(|| panic!("{leaf} event missing product identity: {event:?}"));
            assert_ne!(
                product.get("kind").and_then(|value| value.as_str()),
                Some("executable_facts"),
                "ExecutableFacts is a scheduler fact and must be absent from the public product {leaf} leaf",
            );
        }
    }

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

#[test]
fn product_sessions_publish_balanced_identity_lifecycles() {
    let trace = PublicTrace::compile_requests(TWO_FORMULA_SOURCE, &[None]);
    let mut stack = Vec::new();
    let mut starts = 0;
    for event in trace.events() {
        if named(event, &["fz", "compiler2", "pull", "session", "started"]) {
            starts += 1;
            stack.push(event.metadata["session_id"].as_u64().expect("raw session identity"));
        } else if named(event, &["fz", "compiler2", "pull", "session", "finished"]) {
            let finished = event.metadata["session_id"].as_u64().expect("raw session identity");
            assert_eq!(
                stack.pop(),
                Some(finished),
                "session lifecycles must be properly nested"
            );
        }
    }
    assert!(starts > 0, "production product pulls must announce their session start");
    assert!(stack.is_empty(), "every started session must finish");
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

/// fz-kdt.34's three target fixtures. Chosen by the epic: a convergence-heavy
/// reduce bridge, a predicate search that halts early, and the take/drop/split
/// suite whose 2.6k evaluations make it the widest causal surface in the tree.
const TARGET_FIXTURES: [&str; 3] = [
    "fixtures2/behavior/fz_f98_range_map_converges.fz",
    "fixtures2/behavior/enum_predicate_search.fz",
    "fixtures2/00420_enum_take_drop_split.fz",
];

const SCENARIOS: [&str; 5] = [
    "cold",
    "unchanged",
    "unreachable_edit",
    "reached_leaf_edit",
    "callee_replaced",
];

// (product evaluations, settlements, demanded keys, distinct generations,
// first productions, cross-request recomputations, unexplained evaluations,
// formula evaluations, unexplained formula evaluations)
type RequestBaseline = (u64, u64, usize, u64, u64, u64, u64, u64, u64);
const REQUEST_BASELINES: [[RequestBaseline; 5]; 3] = [
    [
        (2924, 2147, 2082, 2147, 2147, 0, 12, 1217, 0),
        (2725, 2065, 2000, 2065, 2065, 2065, 12, 0, 0),
        (2725, 2065, 2000, 2065, 2065, 2065, 12, 2, 0),
        (2750, 2065, 2000, 2065, 2065, 2065, 12, 116, 39),
        (2751, 2065, 2000, 2065, 2065, 2055, 12, 179, 45),
    ],
    [
        (7461, 5430, 5046, 5269, 5223, 0, 30, 1887, 0),
        (7154, 5348, 4964, 5187, 5141, 5141, 30, 0, 0),
        (7154, 5348, 4964, 5187, 5141, 5141, 30, 2, 0),
        (7218, 5348, 4964, 5187, 5141, 5141, 30, 265, 90),
        (7219, 5348, 4964, 5187, 5141, 5131, 30, 461, 122),
    ],
    [
        (15841, 12309, 11806, 12147, 12053, 0, 27, 3171, 0),
        (15476, 12227, 11724, 12065, 11971, 11971, 27, 0, 0),
        (15476, 12227, 11724, 12065, 11971, 11971, 27, 2, 0),
        (15608, 12227, 11724, 12065, 11971, 11971, 27, 463, 156),
        (15609, 12227, 11724, 12065, 11971, 11961, 27, 643, 185),
    ],
];

const POPULATION_BASELINES: [(u64, u64); 3] = [(62, 0), (168, 32), (239, 38)];

fn target_edit_sequence(fixture: &str) -> (String, [&'static str; 3]) {
    let fixture = std::fs::read_to_string(fixture).unwrap_or_else(|error| panic!("read fixture {fixture}: {error}"));
    let source = fixture.replacen("fn main() do", "fn main() do\n  kdt_reached()", 1);
    (
        format!(
            "fn kdt_unreachable(), do: 0\n\
             fn kdt_old_leaf(), do: 1\n\
             fn kdt_new_leaf(), do: 2\n\
             fn kdt_reached(), do: kdt_old_leaf()\n{source}"
        ),
        [
            "fn kdt_unreachable(), do: 99\n",
            "fn kdt_old_leaf(), do: 3\n",
            "fn kdt_new_leaf(), do: 2\nfn kdt_reached(), do: kdt_new_leaf()\n",
        ],
    )
}

fn assert_product_causes_are_exact_or_explicit(fixture: &str, scenario: usize, report: &CausalReport) {
    let mut unexplained = 0;
    for evaluation in &report.product_evaluations {
        match evaluation.prior_evaluation {
            None => {
                assert_eq!(
                    evaluation.cause,
                    ProductEvaluationCause::Initial,
                    "{fixture} {scenario}"
                );
                assert!(evaluation.triggers.is_empty(), "{fixture} {scenario}");
            }
            Some(previous) => {
                if evaluation.cause == ProductEvaluationCause::Unexplained {
                    unexplained += 1;
                }
                assert_eq!(
                    evaluation.triggers.is_empty(),
                    evaluation.cause == ProductEvaluationCause::Unexplained,
                    "{fixture} {scenario}: {evaluation:?}"
                );
                assert!(
                    evaluation
                        .triggers
                        .iter()
                        .all(|trigger| trigger.position >= previous && trigger.position < evaluation.position),
                    "{fixture} {scenario}: {evaluation:?}"
                );
            }
        }
    }
    assert_eq!(
        unexplained,
        report.product_totals().unexplained_evaluations,
        "{fixture} {scenario}: every unexplained evaluation must remain visible in the aggregate"
    );
}

fn function_id(trace: &PublicTrace, name: &str) -> u64 {
    trace
        .events_named(&["fz", "compiler2", "canon", "function"])
        .into_iter()
        .find(|event| event.metadata_key("canon").and_then(serde_json::Value::as_str) == Some(name))
        .and_then(|event| event.metadata_key("function_id"))
        .and_then(serde_json::Value::as_u64)
        .unwrap_or_else(|| panic!("missing canonical function definition for {name}"))
}

fn value_names_function(value: &serde_json::Value, function: u64) -> bool {
    match value {
        serde_json::Value::Object(fields) => fields.iter().any(|(name, value)| {
            (name == "function_id" && value.as_u64() == Some(function)) || value_names_function(value, function)
        }),
        serde_json::Value::Array(values) => values.iter().any(|value| value_names_function(value, function)),
        _ => false,
    }
}

#[test]
fn target_fixture_reports_exercise_all_five_request_scenarios() {
    for (fixture_index, fixture) in TARGET_FIXTURES.into_iter().enumerate() {
        let (source, edits) = target_edit_sequence(fixture);
        let trace = PublicTrace::compile_requests(&source, &[None, Some(edits[0]), Some(edits[1]), Some(edits[2])]);
        let reports = CausalReport::derive_requests(trace.events());
        assert_eq!(reports.len(), SCENARIOS.len(), "{fixture}");
        let cold = reports[0].product_totals();
        let unchanged = reports[1].product_totals();
        assert!(cold.first_productions > 0, "{fixture}: cold population");
        assert_eq!(cold.cross_request_recomputations, 0, "{fixture}: cold request");
        assert_eq!(
            unchanged.cross_request_recomputations, unchanged.first_productions,
            "{fixture}: unchanged request exposes fresh-session repopulation"
        );
        let irrelevant = reports[2].product_totals();
        assert_eq!(
            irrelevant.cross_request_recomputations, irrelevant.first_productions,
            "{fixture}: an unreachable edit must expose the same fresh-session repopulation"
        );
        assert_eq!(
            reports[1].formula_totals().evaluations,
            0,
            "{fixture}: unchanged scheduler work"
        );
        assert!(
            reports[3].formula_totals().content_caused > 0,
            "{fixture}: reached leaf movement"
        );
        let old_callee = function_id(&trace, "kdt_old_leaf/0");
        let new_callee = function_id(&trace, "kdt_new_leaf/0");
        assert!(
            reports[3]
                .products
                .keys()
                .any(|product| value_names_function(&product.raw, old_callee)),
            "{fixture}: reached request must demand the old callee"
        );
        assert!(
            reports[4]
                .products
                .keys()
                .any(|product| value_names_function(&product.raw, new_callee)),
            "{fixture}: replacement request must introduce the new callee"
        );
        assert!(
            !reports[4]
                .products
                .keys()
                .any(|product| value_names_function(&product.raw, old_callee)),
            "{fixture}: replacement request must withdraw the old callee"
        );
        for (scenario, ((name, report), expected)) in SCENARIOS
            .iter()
            .zip(&reports)
            .zip(REQUEST_BASELINES[fixture_index])
            .enumerate()
        {
            assert_product_causes_are_exact_or_explicit(fixture, scenario, report);
            let product = report.product_totals();
            let formula = report.formula_totals();
            assert_eq!(
                (
                    product.evaluations,
                    product.settlements,
                    report.distinct_demanded_products(),
                    product.distinct_generations,
                    product.first_productions,
                    product.cross_request_recomputations,
                    product.unexplained_evaluations,
                    formula.evaluations,
                    formula.uncaused,
                ),
                expected,
                "{fixture} {name}: causal work baseline"
            );
            assert_eq!(
                (
                    report.final_population.reachable_executables,
                    report.final_population.construction_wrappers,
                ),
                POPULATION_BASELINES[fixture_index],
                "{fixture} {name}: final population"
            );
            assert_eq!(
                report.uncaused.len() as u64,
                formula.uncaused,
                "{fixture} {name}: every unexplained formula evaluation must remain exact in the report"
            );
            assert!(report.readiness_without_settled_wake.is_empty(), "{fixture} {name}");
            assert!(report.undefined_first_uses.is_empty(), "{fixture} {name}");
            assert!(
                report.canon.types() > 0 && report.canon.functions() > 0,
                "{fixture} {name}"
            );
            assert!(report.sessions.sessions > 0, "{fixture} {name}");
            assert_eq!(report.sessions.unsanctioned_work_starts, 0, "{fixture} {name}");
            assert_eq!(report.sessions.root_scans, 0, "{fixture} {name}");
            assert_eq!(
                report.recursive_searches.len() as u64,
                report.recursive_search.searches,
                "{fixture} {name}: every recursive traversal stays exact"
            );
            assert!(
                report
                    .recursive_searches
                    .iter()
                    .all(|search| search.cause.is_some() && search.work.vertex_visits > 0),
                "{fixture} {name}: recursive work belongs to its producer evaluation"
            );
            assert_eq!(
                report
                    .product_publications
                    .iter()
                    .filter(|publication| publication.kind == ProductPublicationKind::RecursiveGroup)
                    .count() as u64,
                product.recursive_members,
                "{fixture} {name}: recursive publications retain exact members"
            );
        }
    }
}

fn compile_fixture(path: &str) -> PublicTrace {
    let source = std::fs::read_to_string(path).unwrap_or_else(|error| panic!("read fixture {path}: {error}"));
    PublicTrace::compile(&source)
}

/// The work one job family did, summed over its per-function formulas, plus
/// how many distinct formulas that family had. `CausalReport` keys formulas by
/// canonical identity (`{"function_id":"main/0","kind":"DeriveCallGraphComponent"}`), so
/// the family is the rows whose kind matches.
fn family_work(report: &CausalReport, kind: &str) -> (u64, FormulaWork) {
    let mut formulas = 0;
    let mut totals = FormulaWork::default();
    for (formula, work) in &report.formulas {
        if !formula.contains(&format!("\"kind\":\"{kind}\"")) {
            continue;
        }
        formulas += 1;
        totals.evaluations += work.evaluations;
        totals.changed_outputs += work.changed_outputs;
        totals.unchanged_outputs += work.unchanged_outputs;
        totals.blocked_completions += work.blocked_completions;
    }
    (formulas, totals)
}

/// fz-kdt.56's ratchet, per target fixture: `(DeriveCallGraphComponent
/// evaluations, evaluations that concluded nothing)`.
///
/// Measured at 1c7201b9b, before the call graph became a fact, the same three
/// fixtures ran 85/47, 83/22 and 165/65 -- one evaluation per BFS layer of
/// each function's own reachable cone, every one of them re-extracting the
/// callees of every body it could already see. The numbers below are what the
/// same compiles do now that the edges are read from `StaticCallees` facts
/// instead.
///
/// fz-kdt.61 renamed the walking job `DeriveRecursive` ->
/// `DeriveCallGraphComponent` and gave it a second output: the same walk now
/// publishes the function's strong-component id alongside the body keying that
/// component decides. The counts below are UNCHANGED by that -- which is the
/// point of folding rather than splitting. A separate component job would have
/// made every function pay one blocked evaluation waiting for its component
/// fact before recursion could conclude, roughly +200 evaluations on
/// enum_take_drop_split; one walk answering both questions costs nothing over
/// the walk that was already there.
/// Per fixture: DeriveCallGraphComponent (evaluations, concluded-nothing),
/// then DeriveStaticCallees (evaluations, blocked) -- the family fz-kdt.56
/// ADDED. Its cost is pinned alongside the family it shrank so the trade stays
/// visible: on enum_take_drop_split the recursion-and-component answer costs
/// 126 + 251 evaluations against 165 before, cheaper per evaluation (fact
/// reads, not cone re-scans) but more of them. The residual blocked
/// completions (24/12/26) are the pull's own layered discovery of the edge
/// facts, which no formulation avoids: a cone cannot be known before it is
/// walked.
///
/// fz-kdt.183 lowered enum_take_drop_split's component row from (134, 34) to
/// (126, 26): `derive_input_demand` waits on `StaticCallees` before it walks
/// anything, so the edge facts a component walk needs are already demanded
/// when it starts and eight of its restarts never happen.
const DERIVE_RECURSIVE_RATCHET: [(&str, u64, u64, u64, u64); 3] = [
    ("fixtures2/behavior/fz_f98_range_map_converges.fz", 62, 24, 101, 51),
    ("fixtures2/behavior/enum_predicate_search.fz", 73, 12, 142, 75),
    ("fixtures2/behavior/enum_take_drop_split.fz", 126, 26, 251, 129),
];

/// fz-kdt.56: recursion is answered from the call graph's edge facts, so
/// discovering a layer costs a fact read instead of a re-scan of every body
/// already known.
///
/// Two halves, and the second is what keeps the first honest:
///
/// - The walking job's restart pyramid shrinks to the pinned counts. The
///   evaluations that conclude nothing -- pure restart cost, 39% of the work on
///   `enum_take_drop_split` before this ticket -- roughly halve.
/// - `DeriveStaticCallees`, the job that replaced the re-scan, publishes each
///   function's edges from exactly ONE evaluation. A body is extracted once no
///   matter how many reachability walks cross it, which is the property the old
///   traversal could not have: it re-extracted per walk, per layer.
///
/// The uncaused check rides along deliberately. A count can also fall by
/// LOSING wakes, and a formula that stopped re-running because its
/// subscriptions no longer reach it would look like an improvement here while
/// being a correctness regression; fz-kdt.34.6's acceptance says every
/// evaluation names a moved input, and it still must.
#[test]
fn deriving_recursion_from_call_graph_facts_extracts_each_body_once() {
    for (fixture, evaluations, concluded_nothing, callee_evaluations, callee_blocked) in DERIVE_RECURSIVE_RATCHET {
        let trace = compile_fixture(fixture);
        assert!(
            matches!(trace.outcome, DriveOutcome::Resolved),
            "{fixture} must resolve for its causal report to describe a whole compile"
        );
        let report = CausalReport::derive(trace.events());

        let (_, recursive) = family_work(&report, "DeriveCallGraphComponent");
        assert_eq!(
            (recursive.evaluations, recursive.unchanged_outputs),
            (evaluations, concluded_nothing),
            "{fixture}: DeriveCallGraphComponent work moved off its fz-kdt.56 pin; re-measure \
             and re-pin with the reason. Full row: {recursive:?}"
        );

        let (functions, callees) = family_work(&report, "DeriveStaticCallees");
        assert!(
            functions > 0,
            "{fixture}: the edge facts must exist for the one-extraction claim to say anything"
        );
        assert_eq!(
            callees.changed_outputs, functions,
            "{fixture}: {functions} functions should have published {functions} edge sets -- one \
             body, one extraction. Full row: {callees:?}"
        );
        assert_eq!(
            callees.evaluations - callees.changed_outputs,
            callees.blocked_completions,
            "{fixture}: every DeriveStaticCallees evaluation that published nothing must be one \
             that blocked waiting for the body; {callees:?}"
        );
        assert_eq!(
            (callees.evaluations, callees.blocked_completions),
            (callee_evaluations, callee_blocked),
            "{fixture}: DeriveStaticCallees work moved off its fz-kdt.56 pin; the family this \
             ticket added must not drift silently. Full row: {callees:?}"
        );

        for (formula, work) in &report.formulas {
            if formula.contains("DeriveStaticCallees") {
                assert_eq!(
                    work.changed_outputs, 1,
                    "{fixture}: {formula} must publish its edge set from exactly one evaluation"
                );
            }
        }

        assert_eq!(
            report.uncaused,
            Vec::new(),
            "{fixture}: the drop must come from doing less work, not from losing the wakes that \
             cause it"
        );
    }
}

/// fz-kdt.63's ratchet, per target fixture: what the analysis's own claims
/// did over a whole compile, and what that cost the schedule.
///
/// `lifecycle` columns are `(distinct facts, first appearances, retractions)`
/// as the stream reports them. `first_appearances > distinct` is the
/// retract-and-remint signature — a claim withdrawn and later re-derived
/// appears out of nothing twice — so the gap between those two columns is
/// the churn that got re-minted. Since fz-kdt.69.1 a withdrawal can STICK
/// (SeedActivation no longer resurrects caller-discovered keys), so the gap
/// can be smaller than the retraction count: retractions that stuck appear
/// only once.
///
/// The two families read differently since fz-kdt.69.2. `Activation` still
/// rides preservation, so its row is the ratchet fz-kdt.63 set. The callsite
/// row no longer can: every callsite the walk REACHES publishes its edge, so
/// preservation of those kinds is gone and the row now measures the WALK —
/// how often the analysis stopped reaching a callsite it had reached before.
struct AnalysisClaimRatchet {
    fixture: &'static str,
    activations: FactLifecycle,
    /// Pinned once; `CallSiteSummary` and `CallSiteTargets` are two answers of
    /// one derivation and must stay in lockstep.
    callsites: FactLifecycle,
    shifts: ShiftWork,
    analyze_evaluations: u64,
    /// Of those, how many concluded with nothing changed -- a whole
    /// re-derivation of one activation that reproduced the answer it already
    /// had. fz-kdt.84 is where this column stopped being mostly self-inflicted;
    /// what is left is fz-kdt.85/.86's to explain.
    analyze_zero_change: u64,
    total_evaluations: u64,
}

const fn lifecycle(distinct: u64, first_appearances: u64, retractions: u64) -> FactLifecycle {
    FactLifecycle {
        distinct,
        first_appearances,
        retractions,
    }
}

const fn shifts(shift_wakes: u64, rebased_completions: u64) -> ShiftWork {
    ShiftWork {
        shift_wakes,
        rebased_completions,
    }
}

/// Measured at 631da1a6d, before analysis claims survived their own silence,
/// the same three compiles ran:
///
/// ```text
///                                 Activation      CallSite*       shifts   Analyze  total
///   fz_f98_range_map_converges    71/77/6         73/75/2         18/28      302     969
///   enum_predicate_search        207/236/29      244/277/33       29/58      849    1667
///   enum_take_drop_split         297/364/67      456/526/70      107/174    1353    2864
/// ```
///
/// The residual retractions on `fz_f98_range_map_converges` are the ones this
/// ticket must NOT remove: they ride rebased conclusions, where the analysis
/// re-derived every claim from ground that genuinely narrowed. That fixture
/// keeping 24 rebased completions while the other two fall to 2 and 10 is what
/// says the narrowing path is still open.
///
/// `fz_f98_range_map_converges` is the one row fz-kdt.69.1 moved, and every
/// number on it fell:
///
/// ```text
///   Activation lifecycle   71/76/5 -> 71/74/5
///   shifts                   17/24 -> 17/19
///   AnalyzeActivation          300 -> 298
///   total evaluations          966 -> 959
/// ```
///
/// Retracting a caller-discovered `Activation(k)` used to route k's own
/// blocked analysis back to `Job::SeedActivation`, which re-minted the key
/// from its own arrow: all five retractions came straight back, and the
/// re-minted claim rebased the analysis again. Two of the five now stick, and
/// the self-gate concludes instead of blocking, so five rebased completions
/// and the work they carried are gone. Nothing was lost with them --
/// `distinct` (71), `retractions` (5), `shift_wakes` (17) and both callsite
/// lifecycles are unchanged, and the other two fixtures' rows do not move at
/// all. That is what rules out the "a count can also fall by LOSING wakes"
/// hazard below: no subscription stopped reaching anyone.
///
/// fz-kdt.69.2 moved the CALLSITE rows and only those, exactly as its ticket
/// pre-authorized:
///
/// ```text
///                                 CallSite* before   after
///   fz_f98_range_map_converges    73/75/2            73/75/2
///   enum_predicate_search        239/239/0          239/272/33
///   enum_take_drop_split         415/415/0          415/427/12
/// ```
///
/// `distinct` does not move on any of the three: every callsite the walk ever
/// reaches was already resolving at some point in the drive, so total emission
/// adds no new key -- it publishes the ones it has earlier, and as
/// `Unresolved`. What appears is retract-and-remint, because the reached-
/// callsite set is NOT monotone: `analyze_tail` stops walking a tail chain at
/// a call with no return evidence yet (an activation key migrating to one
/// whose `ReturnType` has not arrived), so the callsites behind it go
/// unreached for a round and their edges withdraw. Preservation used to hide
/// that. The churn is free -- `Activation`, `shifts`, `AnalyzeActivation` and
/// total evaluations are byte-for-byte what they were, because nothing holds a
/// `Current` subscription on those edges while they move.
///
/// A walk fix (availability per READ -- the rule `entry_scope`'s captures
/// already state, which `analyze_tail` alone does not obey) was measured
/// during fz-kdt.69.2 to remove this churn entirely AND move the executable
/// inventory -- which is that ticket's STOP condition, so it was reverted,
/// not landed. CAUTION: two faithful reconstructions during the adversarial
/// review did NOT reproduce its numbers; the follow-up ticket (fz-kdt on the
/// tail-chain truncation) requires the actual patch as its starting point,
/// not this prose.
///
/// fz-kdt.84 moved the two EVALUATION columns down and nothing else. Deleting
/// the revision mint for a cumulative fact's first claim at bottom stopped
/// `ReturnType`'s empty first claim from waking every `Current` reader of the
/// empty join:
///
/// ```text
///                              AnalyzeActivation   of those, zero-change    total
///   fz_f98_range_map_converges  298 ->  256          85 ->  43        959 ->  917
///   enum_predicate_search       766 ->  655         148 ->  35       1555 -> 1444
///   enum_take_drop_split       1058 ->  946         193 ->  75       2502 -> 2390
/// ```
///
/// The `AnalyzeActivation` delta and the TOTAL delta are the same number on
/// every row (-42, -111, -112): every evaluation that stopped happening was an
/// analysis re-run, and no other family ran less. It comes out of the
/// zero-change column, which is the whole point -- a formula woken by an empty
/// first claim had nothing new to read, so it re-derived the answer it already
/// had. The zero-change column falls slightly FURTHER than the evaluation
/// column on two rows (-113 against -111, -118 against -112) because a few
/// evaluations that used to run before their evidence now run after it and
/// publish: the same content reaching the store in fewer, fuller runs.
///
/// Nothing else moved. Both lifecycles, both shift columns and the emitted
/// executable inventory (`backend_inventory_width_stays_pinned_on_the_target_fixtures`)
/// are what they were, and the three fixtures' canonical
/// backend/types/activations dumps are byte-identical across the change. The
/// claims themselves are untouched -- measured on the same three sources
/// through `fz2 interp --log-telemetry` (a longer drive than this harness's,
/// so its counts are its own), joining each step's
/// `changed[old_revision=null, new_revision=0]` against its `wakes[].cause`:
/// the 46/152/135 empty first claims all still happen, and the 43/137/139
/// `Current` wakes they used to cause are 0.
/// fz-kdt.86 moved the two EVALUATION columns down again, and one `Activation`
/// lifecycle with them. Folding the callee's contract ask together with the
/// facts that key its activation (`require_callee_prerequisites`) collapsed a
/// two-rung wait ladder inside `analyze_activation`'s own body:
///
/// ```text
///                              AnalyzeActivation   of those, zero-change    total
///   fz_f98_range_map_converges  256 ->  226          43 ->  13        917 ->  907
///   enum_predicate_search       655 ->  623          35 ->   4       1444 -> 1434
///   enum_take_drop_split        946 ->  875          75 ->   8       2390 -> 2370
/// ```
///
/// Measured the same way on the longer `fz2 interp --log-telemetry` drive:
/// zero-change analyses 72/43/37 -> 6/13/4 (take_drop/range_map/predicate),
/// of which the FunctionContract-woken 65/30/33 -> 0; no analysis blocked on
/// a callee's contract AND its keying facts together before this change
/// (0/0/0), and 69/31/33 do now. The three facts' surviving wakes are
/// 116/38/66 against the ticket's measured oracle ceiling of 120/38/66 --
/// first-encounter arrivals, not rungs.
///
/// `enum_take_drop_split`'s `Activation` row falls 256 -> 255: with the ladder
/// gone, the caller reaches the callsite with grounded evidence and never
/// mints `Range.reduce_while_step/6` at
/// `(int, int, int, int, {:halt, {list(a4_1_0_e), int}}, a5)` -- a transient
/// specialization keyed on uninstantiated slots. One fewer speculative key is
/// this ticket's direction, and it is invisible downstream: all three
/// fixtures' canonical backend dumps are byte-identical across the change and
/// the emitted inventory holds at 59/221/214
/// (`backend_inventory_width_stays_pinned_on_the_target_fixtures`). Every
/// other column here -- both other lifecycles, both shift columns -- is
/// untouched.
/// fz-kdt.80 moved two of the three rows down again, and this time the
/// CLAIMS moved, not just the evaluations. Intern-time `A ∨ A = A` on the
/// non-tuple DNF axes makes the activation key a join homomorphism, so a
/// callsite reached down several rows stops re-minting a WIDER key than any
/// row walked:
///
/// ```text
///                              Activation   CallSite*    Analyze   total
///   fz_f98_range_map_converges  71 ->  71   73 ->  73   226 -> 226  flat
///   enum_predicate_search      198 -> 174  239 -> 215   623 -> 553  1434 -> 1364
///   enum_take_drop_split       255 -> 219  415 -> 379   875 -> 787  2370 -> 2282
/// ```
///
/// The 24 and 36 `Activation` claims that stopped being published were the
/// re-mint's own inventions: measured on `enum_predicate_search`, the compile
/// published 198 distinct `Activation` facts but ran only 174 distinct
/// `AnalyzeActivation` formulas -- 24 keys nobody ever analysed. At HEAD the
/// two numbers are the same 174. `CallSiteSummary`/`CallSiteTargets` fall by
/// exactly the same 24/36 (retractions unchanged at 33/12): one invented key
/// is one invented edge.
///
/// `analyze_zero_change` on `enum_predicate_search` goes 5 -> 6. That column
/// rising while its own denominator falls 623 -> 553 is a shorter ascent, not
/// more churn: the single new row is `List.reduce_while/3` at
/// `(non_empty_list(int), :none, (int, :none) -> {:cont, :none} | {:halt, _})`,
/// whose evaluations halve 18 -> 9 and whose ninth run reproduces the answer
/// its eighth reached. No formula gained evaluations.
///
/// `fz_f98_range_map_converges` is untouched on every column -- it has no
/// callsite reached down two brand-distinct rows, which is why it was the one
/// fixture with zero lost edge keys before the fix.
/// fz-kdt.106 moved every column of the two moving rows DOWN, and left
/// `fz_f98_range_map_converges` untouched on all of them. A correlated-input
/// row set now absorbs the rows it dominates, so one caller's ascent ladder
/// deposits ONE row instead of one per superseded conclusion:
///
/// ```text
///                              Activation   CallSite*      Analyze   total
///   fz_f98_range_map_converges  71 ->  71   73 ->  73    226 -> 226   flat
///   enum_predicate_search      174 -> 173  215 -> 212    552 -> 539  1363 -> 1350
///   enum_take_drop_split       219 -> 211  378 -> 369    805 -> 742  2300 -> 2237
/// ```
///
/// The `Activation` claims that stopped being published are keys minted from
/// a row set that had crossed `ACTIVATION_INPUT_ROW_BUDGET` and widened to its
/// column-wise join -- one wide key standing where the callers' correlation
/// named narrow ones. `enum_predicate_search` loses exactly one, and its
/// callsite lifecycles fall by the matching three (245 - 248 first appearances
/// against 33 unchanged retractions): a widened key is reached from more than
/// one callsite. `enum_take_drop_split` loses eight, and one retraction with
/// them (12 -> 11) -- a callsite whose target evidence used to withdraw for a
/// round while the wide key was in flight.
///
/// `analyze_zero_change` falls on both moving rows (6 -> 1, 13 -> 9) against
/// denominators that fall too, which is a shorter ascent and not less
/// coverage: an analysis re-run that used to re-derive the answer it already
/// had was reading a row set that had just re-collapsed. Both shift columns
/// are untouched on all three fixtures, and `report.uncaused` stays empty --
/// the drop comes from doing less work, not from losing the wakes that cause
/// it.
///
/// The emitted inventory moves the other way on `enum_take_drop_split`
/// (207 -> 215 executables): fewer analysed keys, more emitted ones, because
/// the keys that survive carry the callers' correlation instead of a widened
/// join. `backend_inventory_width_stays_pinned_on_the_target_fixtures` owns
/// that number and its classification.
const ANALYSIS_CLAIM_RATCHET: [AnalysisClaimRatchet; 3] = [
    AnalysisClaimRatchet {
        fixture: "fixtures2/behavior/fz_f98_range_map_converges.fz",
        // fz-kdt.183: 71 -> 72 distinct with one FEWER retraction (5 -> 4),
        // first appearances flat. The withdrawn key was a joined one that
        // stopped being reachable once the demanded list element split its
        // two users apart; nothing new is minted, one thing stops being
        // unminted.
        //
        // fz-kdt.199: 72 -> 76 distinct, 74 -> 79 first appearances, 4 -> 5
        // retractions. `Range.reduce_cont/6`'s accumulator is a position the
        // activation RETURNS, so its seed and its ascended state stop sharing
        // a key: four more keys, and one more key that is minted before its
        // demand has finished climbing and withdrawn when it does.
        activations: lifecycle(76, 79, 5),
        // fz-kdt.183: 73 -> 74 distinct, 75 -> 76 first appearances,
        // retractions flat -- the recovered activation brings its call edge.
        //
        // fz-kdt.199: 74 -> 85 distinct, 76 -> 87 first appearances,
        // retractions flat -- each activation the returned axis splits brings
        // its own call edges with it.
        callsites: lifecycle(85, 87, 2),
        // fz-kdt.183: 17 -> 30 shift wakes and 19 -> 127 rebased completions.
        // The RISING row of this landing, and the cause is that `InputDemand`
        // is now a fact that MOVES: the forwarded demand of a function whose
        // cone is still filling in climbs the lattice, and every activation
        // keyed off it rebases when it does. It is bounded by the lattice
        // height (a slot rises at most twice) and it buys the split this
        // ticket is for; fz-kdt.196 owns whether the demand can be settled
        // before the first key is minted.
        // fz-kdt.199: 30 -> 31 shift wakes and 127 -> 128 rebased completions.
        // The `returned` axis rides the SAME cone walk on the same reads, so
        // `DeriveInputDemand` runs exactly as often as before (190 evaluations
        // on this fixture, base and head alike); the one extra rebase is the
        // one extra activation minted while its demand was still climbing.
        // fz-tfn.26: rebased completions 128 -> 129. Typed completion order
        // exposes the same standing activation to one additional demand shift;
        // activations and shift wakes stay flat.
        shifts: shifts(31, 129),
        // fz-kdt.183: 226 -> 230 evaluations, 13 -> 14 reproducing an answer
        // they already had -- four more runs for the rebasing above, and
        // `uncaused` stays empty, so every one of them names a moved input.
        //
        // fz-kdt.199: 230 -> 234 evaluations, 14 -> 16 reproducing an answer
        // they already had -- the four extra activations this fixture keys,
        // each analysed once, and `uncaused` still empty.
        // fz-tfn.26: 234 -> 235, with unchanged-output 16 -> 17. The extra
        // rebase above reruns one blocked activation and reproduces its answer;
        // final facts, artifacts, and runtime stay flat.
        analyze_evaluations: 235,
        analyze_zero_change: 17,
        // fz-kdt.199: 1009 -> 1013, the four extra analyses above and nothing
        // else. fz-kdt.45 adds the two exact-executable fact producers.
        // fz-tfn.26 adds the one reproduced analysis above.
        total_evaluations: 1016,
    },
    AnalysisClaimRatchet {
        fixture: "fixtures2/behavior/enum_predicate_search.fz",
        // fz-kdt.106: 174 -> 173. One key minted from a budget-collapsed row
        // set -- the wide `int | :false | :ok | :true` join -- is never minted,
        // because the row set no longer collapses.
        // fz-kdt.127: 173 -> 175. The forwarder erasure keeps capture TYPES,
        // so the `reduce_while/3` chain keys the capture-free `Enum.all?/1`
        // and `any?/1` wrappers apart from the capture-bearing `all?/2` and
        // `any?/2` ones. Two more activations, no retractions.
        // fz-kdt.183: 175 -> 179. The demanded list element splits four
        // reducer activations that used to share one joined key; no
        // retractions, so nothing stopped being published.
        activations: lifecycle(179, 179, 0),
        // fz-kdt.106: 215 -> 212 distinct (248 -> 245 first appearances,
        // retractions unchanged): the one vanished activation was named from
        // three callsites.
        // fz-kdt.127: 212 -> 215 distinct (245 -> 248 first appearances,
        // retractions flat): the two new activations bring their edges.
        // fz-kdt.183: 215 -> 219 distinct (248 -> 252 first appearances,
        // retractions flat): the four new activations bring their edges.
        callsites: lifecycle(219, 252, 33),
        // fz-kdt.183: 1 -> 5 shift wakes, 2 -> 22 rebased completions.
        // `InputDemand` is a fact that MOVES -- a function whose forwarding
        // cone is still filling in publishes a demand that climbs the lattice,
        // and every activation keyed off it rebases when it does. Bounded by
        // the lattice height; fz-kdt.196 owns settling the demand before the
        // first key is minted.
        shifts: shifts(5, 22),
        // fz-kdt.105: 553 -> 552. Canonical clause order at the interner
        // makes one more re-derived union reproduce its previous id instead
        // of minting a permuted twin, so one AnalyzeActivation run that used
        // to see a "changed" input no longer runs at all. The fixture's
        // canonical backend dump is byte-identical either way -- this is
        // work removed, not an answer moved.
        // fz-kdt.106: 552 -> 539. Thirteen analysis runs were re-derivations
        // driven by a row set that kept moving as its ladder accumulated.
        // fz-kdt.127: 539 -> 538. One analysis run fewer: the reducer column
        // that used to arrive as one erased arrow and be re-derived when the
        // second wrapper joined it now arrives already split.
        // fz-kdt.183: 538 -> 549 evaluations. Eleven runs for four new
        // activations and the rebasing above; `uncaused` stays empty, so every
        // one of them names a moved input.
        // fz-tfn.26: 549 -> 548. Typed activation ordering makes the second
        // `List.reduce_while_step/3` return ascent and the corresponding
        // `List.reduce_while_cont/3` input ascent land before one queued
        // analysis runs. The one run now observes both content movements;
        // every other formula-family count and the final artifacts stay flat.
        analyze_evaluations: 548,
        // fz-kdt.91: with clause lists canonical (source order), one
        // completion that used to publish a spuriously "changed"
        // EntryReachability (same clause set, new arrival order) now
        // publishes it unchanged -- evaluations flat, one fewer
        // downstream wake. 4 -> 5.
        // fz-kdt.80: 5 -> 6, against a denominator that fell 623 -> 553.
        // See the header: one formula's ascent shortened 18 -> 9 runs and
        // its last run reproduces the answer.
        // fz-kdt.106: 6 -> 1, against a denominator that fell 552 -> 539.
        // fz-kdt.183: 1 -> 3, against a denominator that rose 538 -> 549.
        analyze_zero_change: 3,
        // 1364 -> 1363: the same single evaluation, seen from the whole-run
        // denominator. fz-kdt.106: 1363 -> 1350, the same thirteen.
        // fz-kdt.127: 1350 -> 1349, the same single evaluation.
        // fz-kdt.183: 1349 -> 1381. fz-kdt.45 adds the two exact-executable
        // fact producers.
        // fz-tfn.26: 1383 -> 1382, the one coalesced content-caused analysis
        // above; no other formula family moves.
        total_evaluations: 1382,
    },
    AnalysisClaimRatchet {
        fixture: "fixtures2/behavior/enum_take_drop_split.fz",
        // fz-kdt.106: 219 -> 211. Eight keys minted from a budget-collapsed
        // row set are never minted, because the row sets no longer collapse.
        // fz-kdt.132: 211 -> 250. A RISE, and it is the ascent this fixture
        // was never finishing. A fold's reducer used to be clamped onto the
        // specialization it was minted beside, so its accumulator stopped one
        // rung short of the value the fold produces; unclamped, each fold
        // climbs its last rung and every activation on that rung is new. The
        // rise is bounded by the ladder's height (+39 on 211, no retractions,
        // no uncaused work) and it BUYS the executables it costs: the emitted
        // inventory falls 215 -> 196 in the same motion, because the three
        // partial rungs per reducer collapse into the one grown accumulator.
        // fz-kdt.127: 250 -> 258. Same cause as `enum_predicate_search`, on
        // the same chain: capture-free `take_positive`/`drop_positive` key
        // apart from `take_every`/`drop_every`, which close over the step.
        // Eight more activations, no retractions.
        // fz-kdt.183: 258 -> 259. One reducer activation splits off the
        // joined key; no retractions.
        // fz-kdt.192: 259 -> 256. A FALL. A parameter position now observes
        // its ARGUMENT rather than the pattern restated, so the empty-list
        // veto reads the `[]` the call really supplied. On this fixture
        // exactly eight callsite rows change verdict and every one falls
        // `Known` -> `Underconstrained`; no row rises. Four are
        // `List.reduce_while_step/3`, whose `{:cont, b} | {:halt, c}`
        // accumulator arrives as `{:cont, [int]} | {:halt, []}`: that `[]`
        // used to pin `c = []` and the row claimed `result = [] | [int]` as a
        // runtime fact, and `c` is now honestly free. Four are tuple
        // parameters -- `{[a], [a]}` twice, `{[a], [a], int}` once and
        // `{[a], :false | :true}` once -- where the `[]` one field or one
        // union alternative supplies vetoes `a` for the WHOLE position and
        // discards the `[int]` its sibling proved (fz-f98.16's D3, a precision
        // loss). A row that no longer reports a narrowed parameter surface
        // refines no caller input, so three fewer distinct activation keys are
        // minted. The two causes are independent and they compose: 183 adds
        // one activation by splitting a joined key, this removes three by not
        // publishing a narrowed surface.
        // fz-kdt.199: 256 -> 267 -- the accumulators of the reduce families
        // this fixture drives key their seed apart from their ascent.
        // fz-kdt.120: 267 -> 271, a RISE, and it is fz-kdt.192's FALL being
        // repaid rather than a new cost. 192 booked 259 -> 256 with the reason
        // written above: four tuple parameters -- `{[a], [a]}` twice,
        // `{[a], [a], int}` once, `{[a], :false | :true}` once -- where one
        // field's `[]` vetoed `a` for the WHOLE position and discarded the
        // `[int]` a sibling field had proved, so those rows published no
        // narrowed parameter surface and three fewer keys were minted. The veto
        // is gone, the join absorbs `[]` instead of vetoing on it (`join(none,
        // int) = int`, pinned as X6 agreeing with X6B), and those positions
        // publish their narrowed surface again. What the four extra keys BUY is
        // on the artifact: `List.reduce_while_step/3` now keys on the
        // accumulator the fold really carries, `{:cont | :halt, []} |
        // {:cont, [int]}`, instead of the veto's `{:cont, [int]}` with the seed
        // rung erased. Executables are FLAT at 237 and interp and run stdout
        // are byte-identical to base, so this is compile work rising on the
        // arc's slowest fixture and nothing else; retractions stay 0.
        // fz-kdt.47: 271 -> 270. Creating typed callable resolutions before
        // wrapper seating means the transient `Enum.drop_positive_finish/1`
        // specialization at `({empty_list, int})` is never minted. This is a
        // strict work deletion; no standing key is withdrawn.
        activations: lifecycle(270, 270, 0),
        // fz-kdt.105: 379 -> 378 distinct (391 -> 390 first appearances). The
        // narrowed `drop_while` accumulator leaves one fewer distinct callsite
        // summary -- the wide arm the four lambda specializations were keyed on
        // is no longer a destination anywhere.
        // fz-kdt.106: 378 -> 369 distinct, 390 -> 380 first appearances, and
        // one retraction with them (12 -> 11): the eight vanished activations
        // take their edges, and the callsite whose evidence withdrew for a
        // round while a widened key was in flight no longer does.
        // fz-kdt.132: 369 -> 425 distinct, 380 -> 441 first appearances,
        // 11 -> 16 retractions -- the 39 new activations bring their call
        // edges, and a callsite that names a climbing accumulator withdraws
        // its edge for the round the previous rung is displaced in.
        // fz-kdt.127: 425 -> 434 distinct (441 -> 450 first appearances,
        // retractions flat): the eight new activations bring their edges.
        // fz-kdt.192: 434 -> 430 distinct (450 -> 445 first appearances,
        // 16 -> 15 retractions). The three vanished activations take their
        // edges, and one callsite no longer withdraws an edge for a round.
        // fz-kdt.199: 430 -> 455 distinct, 445 -> 473 first appearances,
        // 15 -> 18 retractions -- each split activation brings its call edges,
        // and three more edges withdraw while a demand is still climbing.
        // fz-kdt.120: 455 -> 460 distinct, 473 -> 471 first appearances, and
        // retractions FALL 18 -> 11. The four extra activations bring their
        // edges, and seven fewer edges withdraw: a `List.reduce_while_step/3`
        // key that names the fold's seed rung from the start is not displaced
        // as the accumulator climbs, so the callsites that name it stop
        // withdrawing for a round while a widened key is in flight. Fewer
        // first appearances alongside more distinct rows is the same fact --
        // rows that used to be minted, withdrawn and re-minted are minted once.
        // fz-kdt.47: 460 -> 459 distinct and 471 -> 470 first appearances.
        // The transient activation removed above takes its one callsite with
        // it; retractions stay flat.
        // fz-tfn.26: distinct stays 459 while 470/11 -> 469/10. Typed
        // activation order removes one transient retract/remint of an already
        // final identity; the final inventory does not move.
        callsites: lifecycle(459, 469, 10),
        // fz-kdt.183: 6 -> 25 shift wakes, 10 -> 77 rebased completions --
        // the moving `InputDemand` fact, same cause as on
        // `enum_predicate_search` above. fz-kdt.192 leaves this row FLAT:
        // withdrawing a narrowed parameter surface changes which activation
        // keys exist, not how often `InputDemand` moves under them.
        // fz-kdt.47: rebased completions 77 -> 76. The transient activation
        // removed above never needs its rebase.
        shifts: shifts(25, 76),
        // fz-kdt.105: 787 -> 805, zero-change 8 -> 13, total 2282 -> 2300. The
        // one RISING row in this landing, and it is the price of the precision
        // the same change bought: the accumulator that used to widen to
        // `{[int], :false} | {[int], :true}` now settles at `{[], :true} |
        // {[int], :false}`, and a narrower carried type takes more rungs to
        // reach its fixed point than a widened one does. Emitted executables
        // fall 211 -> 207 in the same motion. Not the ladder running away: the
        // run still settles, the artifact is behaviourally identical, and the
        // rise is bounded (+18 on 219 activations). Traced further in fz-kdt.110.
        // fz-kdt.106: 805 -> 742, zero-change 13 -> 9, total 2300 -> 2237. The
        // rise fz-kdt.105 booked is repaid: an accumulating row set re-ran its
        // activation once per rung, and the rungs are gone.
        // fz-kdt.132: 742 -> 880, total 2237 -> 2375, zero-change FLAT at 9.
        // The last rung of every fold's accumulator now gets analyzed, which
        // is work that was never done rather than work repeated -- flat
        // zero-change is the evidence: not one of the 138 added runs
        // reproduces an answer it already had.
        // fz-kdt.127: 880 -> 890, total 2375 -> 2385, zero-change 9 -> 8. Ten
        // runs for eight new activations, and one FEWER reproduces an answer
        // it already had: the split reducer columns arrive settled instead of
        // being re-derived as the second lambda joins them.
        // fz-kdt.183: 890 -> 900 evaluations, 8 -> 16 reproducing an answer
        // they already had, total 2385 -> 2423. The rebasing above is the
        // whole of it; `uncaused` is empty.
        // fz-kdt.192: 900 -> 889 evaluations, total 2423 -> 2412, zero-change
        // 16 -> 15. All FALLS, and the same cause as the activation row above:
        // three fewer activations are three fewer analyses to run, and one
        // fewer run reproduces an answer it already had.
        // fz-kdt.199: 889 -> 921 evaluations, 15 -> 14 reproducing an answer
        // they already had, 2412 -> 2444 total -- one analysis per activation
        // the returned axis splits, and `uncaused` stays empty.
        //
        // This lens UNDERSTATES the cost on this fixture by an order of
        // magnitude, and the honest number belongs beside it:
        // `fz.compiler2.pull.product.settled` goes 9815 -> 12406 (+26%) here,
        // against +32 on the analysis evaluations this row counts. The
        // formula-evaluation census counts a job RUN; a settle counts a pull
        // reaching a settled answer, and each extra activation is pulled
        // through by every consumer that reaches it. Wall clock does not track
        // it either way: best of 5 `interp` runs on this fixture is 463 ms at
        // base against 452 ms here, and no claim that the landing is FASTER
        // survives that spread. The settle count, not the clock, is what this
        // ticket spends. fz-kdt.213's subtraction is what pays it back.
        // fz-kdt.120: 921 -> 935 evaluations, zero-change 14 -> 15, and
        // `uncaused` stays 0 -- no wake was lost. Fourteen runs for four new
        // activations, because an activation is analyzed once per consumer
        // that pulls it through and the widened
        // `List.reduce_while_step/3` accumulator has several. This is the same
        // spend the row already books for 105 and 199 and it is bounded: one
        // more run reproduces an answer it already had, retractions FALL 18 ->
        // 11, executables are flat at 237, and stdout is byte-identical on
        // interp and run.
        // fz-kdt.47: 935 -> 933. The removed transient activation had two
        // analysis passes; zero-change stays flat at 15.
        // fz-tfn.26: 933 -> 918 and total 2458 -> 2443. Fifteen content
        // ascents now coalesce before their analyses run. The unchanged-output
        // count stays 15, every other formula family stays flat, and the final
        // artifact/runtime gates below remain the authority on coverage.
        analyze_evaluations: 918,
        analyze_zero_change: 15,
        // The deleted analysis passes are the .47 whole-run fall; fz-kdt.45's
        // two exact-executable fact producers bring the total to 2458 before
        // typed ordering removes the fifteen analyses above.
        total_evaluations: 2443,
    },
];

/// fz-kdt.63: an analysis that could not name a callee this run withdraws
/// nothing.
///
/// The churn this pins away was entirely self-inflicted. A callsite whose
/// target evidence was still climbing resolved to nothing, so the run emitted
/// no `Activation` for it; plain output replacement read that silence as a
/// WITHDRAWAL, which is a ground shift, which rebases every reader — who then
/// re-derive, re-mint the same claims, and shift their own readers in turn.
/// Absence is bottom, not retraction; only a rebased conclusion, which
/// re-derived from moved ground, may narrow. Since fz-kdt.69.2 that reading
/// applies to `Activation` alone: the callsite edges publish unconditionally,
/// so their row is a measurement of the walk, not of preservation.
///
/// The uncaused check rides along because a count can also fall by LOSING
/// wakes: a formula that stopped re-running because its subscriptions no
/// longer reach it would read as an improvement here while being a
/// correctness regression.
#[test]
fn analysis_claims_survive_a_run_that_could_not_re_derive_them() {
    for row in ANALYSIS_CLAIM_RATCHET {
        let AnalysisClaimRatchet {
            fixture,
            activations,
            callsites,
            shifts,
            analyze_evaluations,
            analyze_zero_change,
            total_evaluations,
        } = row;
        let trace = compile_fixture(fixture);
        assert!(
            matches!(trace.outcome, DriveOutcome::Resolved),
            "{fixture} must resolve for its causal report to describe a whole compile"
        );
        let report = CausalReport::derive(trace.events());
        let (executable_fact_formulas, executable_fact_work) = family_work(&report, "DeriveExecutableFacts");
        assert_eq!(
            (
                executable_fact_formulas,
                executable_fact_work.evaluations,
                executable_fact_work.changed_outputs
            ),
            (2, 2, 2),
            "{fixture}: the +2 total is exactly the two World fact producers that replaced the product formula: \
             {executable_fact_work:?}",
        );
        let lifecycle_of = |kind: &str| report.lifecycles.get(kind).cloned().unwrap_or_default();

        assert_eq!(
            lifecycle_of("Activation"),
            activations,
            "{fixture}: Activation claims moved off their fz-kdt.63 pin"
        );
        assert_eq!(
            lifecycle_of("CallSiteSummary"),
            callsites,
            "{fixture}: CallSiteSummary claims moved off their fz-kdt.63 pin"
        );
        assert_eq!(
            lifecycle_of("CallSiteTargets"),
            callsites,
            "{fixture}: CallSiteTargets must move in lockstep with CallSiteSummary -- they are two \
             answers of one derivation"
        );
        assert_eq!(
            report.shifts, shifts,
            "{fixture}: ground-shift traffic moved off its fz-kdt.63 pin"
        );

        let (_, analyze) = family_work(&report, "AnalyzeActivation");
        assert_eq!(
            (analyze.evaluations, analyze.unchanged_outputs),
            (analyze_evaluations, analyze_zero_change),
            "{fixture}: AnalyzeActivation work moved off its fz-kdt.63/.84 pin. Full row: {analyze:?}"
        );
        assert_eq!(
            report.formula_totals().evaluations,
            total_evaluations,
            "{fixture}: total formula evaluations moved off their fz-kdt.63 pin"
        );

        assert_eq!(
            report.uncaused,
            Vec::new(),
            "{fixture}: the drop must come from doing less work, not from losing the wakes that \
             cause it"
        );
    }
}

/// A callee whose `@spec` makes it a contract-declaring function. Analyzing
/// `main` reaches the call while `M.helper/1` has neither its contract nor
/// the facts that key its activation.
const CONTRACT_CALLEE_SOURCE: &str =
    "defmodule M do\n  @spec helper(integer) :: integer\n  fn helper(x), do: x + 1\nend\nfn main(), do: M.helper(41)\n";

/// The function-keyed facts a completion reports itself blocked on, as
/// `"Kind(function_id)"` — kind plus `function_id` is the whole identity the
/// public stream renders for `FunctionContract`/`Recursive`/`InputDemand`.
fn blocked_function_facts(completion: &serde_json::Value) -> std::collections::HashSet<String> {
    let Some(blocked) = completion.get("blocked").and_then(|v| v.as_array()) else {
        return std::collections::HashSet::new();
    };
    blocked
        .iter()
        .filter_map(|fact| {
            let kind = fact.get("kind")?.as_str()?;
            let function = fact.get("function_id")?.as_u64()?;
            Some(format!("{kind}({function})"))
        })
        .collect()
}

/// The raw id the public stream gave the function `label` names. The
/// `canon.function` definition lines are the stream's own id dictionary.
fn function_id_named(trace: &PublicTrace, label: &str) -> u64 {
    trace
        .events_named(&["fz", "compiler2", "canon", "function"])
        .iter()
        .find(|ev| ev.metadata_key("canon").and_then(|v| v.as_str()) == Some(label))
        .and_then(|ev| ev.metadata_key("function_id")?.as_u64())
        .unwrap_or_else(|| panic!("expected the public stream to define a canon.function line for {label}"))
}

/// fz-kdt.86: a callee's prerequisites are ONE ask, never a ladder.
///
/// Before a call to `M.helper/1` can resolve, the callee's contract must be
/// applied to the surface AND the facts that key its activation
/// (`Recursive`, `InputDemand`) must exist. When the analysis first reaches
/// the callsite none of the three is there yet. Waits are AND-satisfied, so
/// naming all three in one completion costs exactly one block and one wake;
/// asking for the contract alone and reaching the keying facts only on the
/// next run is a two-rung ladder that re-runs the whole analysis to learn
/// what it could have asked for in the first place.
///
/// The intent is the SHAPE of the ask, not a count of jobs: the analysis may
/// block on other things and re-run for other reasons, but it must never
/// spend two blocks on one callee's prerequisites.
#[test]
fn an_analysis_asks_for_a_callees_contract_and_keying_facts_in_one_block() {
    let trace = PublicTrace::compile(CONTRACT_CALLEE_SOURCE);
    assert!(
        matches!(trace.outcome, DriveOutcome::Resolved),
        "the contract-callee source must compile for its blocks to describe a whole drive"
    );

    let helper = function_id_named(&trace, "M.helper/1");
    let prerequisites = ["FunctionContract", "Recursive", "InputDemand"]
        .into_iter()
        .map(|kind| format!("{kind}({helper})"))
        .collect::<std::collections::HashSet<_>>();

    let blocks = trace
        .events_named(&["fz", "compiler2", "work_graph", "applied"])
        .into_iter()
        .filter_map(|ev| {
            let completion = ev.metadata_key("completion")?;
            if completion.get("kind").and_then(|v| v.as_str()) != Some("AnalyzeActivation") {
                return None;
            }
            let blocked = blocked_function_facts(completion);
            (!blocked.is_disjoint(&prerequisites)).then_some(blocked)
        })
        .collect::<Vec<_>>();

    assert_eq!(
        blocks.len(),
        1,
        "an analysis must spend exactly ONE block on M.helper/1's prerequisites; \
         each extra block is a rung of a ladder. Blocks seen: {blocks:?}"
    );
    assert!(
        blocks[0].is_superset(&prerequisites),
        "the single block must name the contract AND both keying facts together, \
         so one wake satisfies them all. Named: {:?}, required: {prerequisites:?}",
        blocks[0]
    );
}
