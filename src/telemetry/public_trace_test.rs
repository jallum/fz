use super::*;
use crate::compiler2::{WorkLedger, WorkStartReason};
use crate::telemetry::causal::{
    CausalReport, FactLifecycle, FormulaWork, ProductEvaluationCause, ProductEvaluationTriggerKind,
    ProductPublicationKind, PublicEvent, ShiftWork,
};
use crate::telemetry::handler::EventKind;
use fz_engine::DriveOutcome;

/// The ticket's acceptance scenario: two functions, one calling the other.
/// `main/0` is required — `PublicTrace::compile` closes it as the root, the
/// same way `fz2 run`/`interp`/`build` do.
const TWO_FORMULA_SOURCE: &str = "def helper(x), do: x + 1\ndef main(), do: helper(41)\n";

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
fn runtime_demand_body_walks_are_work_not_formula_identity() {
    let mut events = ReplayEvents::default();
    for evaluations in [0, 1, 3] {
        events.applied(serde_json::json!({
            "kind": "DeriveRuntimeDemand", "root_id": 1,
            "runtime_demand_evaluations": evaluations
        }));
    }
    let report = CausalReport::derive(&events.0);
    assert_eq!(
        report.formulas.len(),
        1,
        "changing work counts must not create another formula"
    );
    let work = report.formula_totals();
    assert_eq!(work.evaluations, 3, "the prerequisite wait is still a completed job");
    assert_eq!(
        work.runtime_demand_evaluations, 4,
        "count actual walks, including local repeats"
    );
    assert_eq!(
        (work.initial, work.uncaused),
        (1, 2),
        "a changed count is not new input evidence"
    );
}

#[test]
fn product_dependency_movement_attributes_only_its_exact_consumer() {
    let dependency = |owner, kind| {
        serde_json::json!({
            "kind": "Product", "root_id": owner,
            "product": {"kind": kind, "root_id": 9}
        })
    };
    let wanted = dependency(7, "root_backend_product");
    for (moved, expected) in [
        (wanted.clone(), 1),
        (dependency(8, "root_backend_product"), 0),
        (dependency(7, "native_program"), 0),
    ] {
        let mut events = ReplayEvents::default();
        events.applied(serde_json::json!({
            "kind": "ScopeCode", "source_owner": 1, "blocked": [wanted]
        }));
        let mut change = moved.clone();
        change["old_revision"] = serde_json::json!(3);
        change["new_revision"] = serde_json::json!(3);
        change["old_settled"] = serde_json::json!(false);
        change["new_settled"] = serde_json::json!(true);
        let mut wake = moved.clone();
        wake["use"] = serde_json::json!("settled");
        events.push(
            &["work_graph", "dependencies_moved"],
            serde_json::json!({
                "step": {
                    "changed": [change], "movements": [moved],
                    "wakes": [{"cause": wake, "job": {"kind": "ScopeCode", "source_owner": 1},
                        "admission": "started", "shift": false}], "blocked": []
                }
            }),
        );
        events.applied(serde_json::json!({"kind": "ScopeCode", "source_owner": 1}));
        let report = CausalReport::derive(&events.0);
        let work = report.formula_totals();
        assert_eq!(
            work.evaluations, 2,
            "the dependency movement is not a formula evaluation"
        );
        assert_eq!(work.readiness_caused, expected);
        assert_eq!(
            work.uncaused,
            1 - expected,
            "owner and product are both required for attribution"
        );
        assert!(report.readiness_without_settled_wake.is_empty());
    }
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
            text: "def main(), do: 0\n".to_string(),
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
        events.request(&serde_json::json!({"kind": "synthetic", "arrow": arrow}));
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
fn canonical_recursive_groups_preserve_partitions_not_session_local_numbers() {
    let report = |sessions: [u64; 2], groups: [Option<u64>; 4], nested| {
        let mut events = ReplayEvents::default();
        events.session("started", sessions[0]);
        for (index, group) in groups.into_iter().enumerate() {
            if index == 2 && nested {
                events.session("started", sessions[1]);
            }
            events.push(
                &["pull", "product", "settled"],
                serde_json::json!({
                    "product": {"kind": "synthetic", "member": index},
                    "settlement": {"generation": 1, "changed": true, "group": group},
                }),
            );
        }
        if nested {
            events.session("finished", sessions[1]);
        }
        events.session("finished", sessions[0]);
        CausalReport::derive(&events.0).canonical_multiset()
    };

    let paired = report([1, 2], [Some(1); 4], true);
    assert_eq!(
        paired,
        report([8, 9], [Some(42), Some(42), Some(7), Some(7)], true),
        "group and session allocation order is not identity"
    );
    assert_ne!(
        paired,
        report([1, 2], [Some(1), Some(2), Some(1), Some(1)], true),
        "equal product counts must not hide a split publication group"
    );
    assert_ne!(
        report([1, 2], [Some(1), Some(2), Some(1), Some(1)], true),
        report([1, 2], [None, Some(2), Some(1), Some(1)], true),
        "a singleton recursive publication is not an ordinary settlement"
    );
    assert_ne!(
        report([1, 2], [Some(1), Some(1), Some(2), Some(2)], false),
        report([1, 2], [Some(1), Some(2), Some(1), Some(2)], false),
        "AB/CD and AC/BD have equal group sizes but different exact membership"
    );
}

#[test]
fn canonical_recursive_groups_retain_equal_member_and_publication_multiplicity() {
    let mut events = ReplayEvents::default();
    for arrow in [1, 2] {
        events.push(
            &["canon", "type"],
            serde_json::json!({"type_id": arrow, "canon": "int"}),
        );
    }
    for group in [1, 2] {
        events.session("started", 1);
        for arrow in [1, 2] {
            events.push(
                &["pull", "product", "settled"],
                serde_json::json!({
                    "product": {"kind": "synthetic", "arrow": arrow},
                    "settlement": {"generation": 1, "changed": group == 1, "group": group},
                }),
            );
        }
        events.session("finished", 1);
    }
    let report = CausalReport::derive(&events.0);
    assert_eq!(
        report.recursive_groups.len(),
        2,
        "retained session reactivation keeps distinct publications"
    );
    let groups = report
        .canonical_multiset()
        .into_iter()
        .filter(|(key, _)| key.starts_with("recursive_group\u{1}"))
        .collect::<Vec<_>>();
    assert_eq!(
        groups,
        vec![("recursive_group\u{1}[0,0]".to_string(), 2)],
        "equivalent raw members and repeated groups both retain multiplicity"
    );
}

#[test]
fn canonical_product_causality_distinguishes_live_fact_use_modes() {
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
    assert_ne!(current, settled);
}

fn named(ev: &PublicEvent, name: &[&str]) -> bool {
    ev.name.iter().map(String::as_str).eq(name.iter().copied())
}

/// The public trace tells the causal story of a compile: code is indexed,
/// jobs supply semantic facts, products compose the backend, and the exact
/// root product settles before its request finishes. This test proves
/// that story is readable from the *public* stream alone — the same stream
/// `fz2 --log-telemetry` writes in production.
#[test]
fn compile_reports_resolved_and_an_ordered_causal_chain() {
    let trace = PublicTrace::compile_requests(TWO_FORMULA_SOURCE, &[]);

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
    let first_job_start = trace
        .events()
        .iter()
        .position(|ev| ev.kind == EventKind::SpanStart && named(ev, &["fz", "compiler2", "job"]))
        .expect("expected at least one fz.compiler2.job span_start");
    let first_product_settled = first_index(&["fz", "compiler2", "pull", "product", "settled"]);
    let root_settled = trace
        .events()
        .iter()
        .position(|event| {
            named(event, &["fz", "compiler2", "pull", "product", "settled"])
                && event.metadata["product"]["kind"] == "root_backend_product"
        })
        .expect("the requested backend root must settle");
    let first_completion = first_index(&["fz", "compiler2", "work_graph", "applied"]);
    let request_finished = first_index(&["fz", "compiler2", "backend_request", "finished"]);

    assert!(
        first_job_start < first_completion && first_completion < first_product_settled,
        "semantic jobs must supply facts before artifact production can settle"
    );
    assert!(
        first_product_settled < root_settled,
        "backend prerequisites must settle before the composed root product"
    );
    assert!(
        root_settled < request_finished,
        "the requested root must settle before the request reports success"
    );
    let report = CausalReport::derive(trace.events());
    assert_eq!(report.formula_totals().uncaused, 0);
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
    let known_span_ids: crate::fast_hash::HashSet<u64> = spans.iter().map(|span| span.span_id).collect();
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

/// `fz.compiler2.job` owns timing and job identity; `work_graph.applied` owns
/// the completed formula's causal payload. Keeping the successful span stop
/// payload-free prevents the same `World` and `JobCompletion` from being
/// rendered twice while preserving both public signals.
#[test]
fn job_span_is_the_clock_and_work_graph_applied_is_the_completion_owner() {
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
            stop.metadata_key("completion").is_none(),
            "job span_stop must not duplicate work_graph.applied completion metadata: {:?}",
            stop.metadata
        );
        assert!(
            stop.metadata_key("world").is_none(),
            "job span_stop must not duplicate work_graph.applied world metadata: {:?}",
            stop.metadata
        );
        assert!(
            stop.measurements.get("elapsed_ns").and_then(|v| v.as_u64()).is_some(),
            "job span_stop measurements missing numeric \"elapsed_ns\": {:?}",
            stop.measurements
        );
    }

    let completions = trace.events_named(&["fz", "compiler2", "work_graph", "applied"]);
    assert!(!completions.is_empty(), "expected work_graph.applied completions");
    for event in completions {
        assert!(event.metadata_key("world").is_some());
        assert!(event.metadata_key("completion").is_some());
    }
}

/// The identity portion of a `work_graph.applied` completion object — its
/// `"kind"` plus id fields — with the non-identity fields (`opaque_type`,
/// `rebased`, the derivation volume, and the applied-step batches) stripped out. Lets a test
/// compare "this job" (as `wakes[].job` renders it) against "this
/// completion" (as the top-level `JobCompletion` opaque body renders it)
/// even though the two renderers include a different set of surrounding
/// keys.
fn completion_job_identity(completion: &serde_json::Value) -> serde_json::Value {
    fact_identity(
        completion,
        &[
            "opaque_type",
            "rebased",
            "activation_input_refolds",
            "derivations",
            "reads_handed",
            "retired",
            "changed",
            "wakes",
            "movements",
            "blocked",
        ],
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
/// admission is the woken job's real work start, and a later
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
        wake.get("admission").and_then(|v| v.as_str()),
        Some("started"),
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
    "def identity(x), do: x\ndef main() do\n  identity(1)\n  identity(:atom)\nend\n";

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

    let mut arrows_by_function: crate::fast_hash::HashMap<u64, crate::fast_hash::HashSet<u64>> =
        crate::fast_hash::HashMap::default();
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

/// Public settlement payloads and their sibling cache-hit registration both render.
/// Multiple independent executable products exercise distinct settlement keys;
/// an explicit unchanged request exercises retained reuse without incidental work.
#[test]
fn public_settled_and_retained_cache_hit_events_keep_their_typed_payloads() {
    let trace = PublicTrace::compile_requests(SAME_FUNCTION_TWO_TYPES_SOURCE, &[None]);
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

    // Independent executable products each report their own settlement.
    let backend_executable_keys: crate::fast_hash::HashSet<String> = settled
        .iter()
        .filter_map(|ev| ev.metadata_key("product"))
        .filter(|product| product.get("kind").and_then(|v| v.as_str()) == Some("backend_executable"))
        .map(|product| product.to_string())
        .collect();
    assert!(
        backend_executable_keys.len() > 1,
        "expected more than one distinct settled backend_executable product key, got {backend_executable_keys:?}"
    );

    // (c) the allowlist addition is observable: cache_hit is public.
    let cache_hits = trace.events_named(&["fz", "compiler2", "pull", "product", "cache_hit"]);
    assert!(!cache_hits.is_empty(), "expected at least one public cache_hit event");
    assert!(
        cache_hits.iter().any(|event| event
            .metadata_key("product")
            .and_then(|product| product.get("kind"))
            .and_then(|kind| kind.as_str())
            == Some("root_backend_product")),
        "the explicit unchanged request observes the retained root hit"
    );
}

#[test]
fn session_finish_reports_one_work_start_count_per_reason() {
    let trace = PublicTrace::compile_requests("def main(), do: 1\n", &[None]);
    let finished: Vec<_> = trace
        .events()
        .iter()
        .filter(|event| named(event, &["fz", "compiler2", "pull", "session", "finished"]))
        .collect();
    assert!(
        !finished.is_empty(),
        "a compile publishes at least one finished session"
    );
    let expected: Vec<&str> = {
        let mut names: Vec<&str> = WorkStartReason::TELEMETRY_ORDER
            .iter()
            .map(|reason| reason.name())
            .collect();
        names.sort_unstable();
        names
    };
    for event in finished {
        let starts = event.metadata["session"]["work_starts"]
            .as_object()
            .expect("the session carries its work starts as one object");
        let mut keys: Vec<&str> = starts.keys().map(String::as_str).collect();
        keys.sort_unstable();
        assert_eq!(keys, expected, "every reason appears, none is left out");
    }
}

/// Every finished session reports the request accounting beside its runs:
/// one count per reason for jobs started, requests that found their job
/// already pending, and started jobs parked again. A started job is run or
/// parked again at most once; jobs still queued when a session ends are in
/// neither, so the sum never exceeds the started count.
#[test]
fn session_finish_reports_request_counts_beside_its_runs() {
    let trace = PublicTrace::compile_requests(TWO_FORMULA_SOURCE, &[None]);
    let finished: Vec<_> = trace
        .events()
        .iter()
        .filter(|event| named(event, &["fz", "compiler2", "pull", "session", "finished"]))
        .collect();
    assert!(!finished.is_empty());
    for event in finished {
        let requests = event.metadata["session"]["requests"]
            .as_object()
            .expect("the session carries its request counts as one object");
        let mut ledgers: Vec<&str> = requests.keys().map(String::as_str).collect();
        ledgers.sort_unstable();
        assert_eq!(ledgers, ["already_pending", "reparked", "started"]);
        for ledger in requests.values() {
            assert_eq!(
                ledger.as_object().expect("a count per reason").len(),
                WorkStartReason::TELEMETRY_ORDER.len(),
                "every reason appears in every ledger"
            );
        }
    }

    let report = CausalReport::derive(trace.events());
    let ledger = report.sessions.ledger;
    assert!(ledger.ran.total() > 0, "the compile ran jobs");
    for reason in WorkStartReason::TELEMETRY_ORDER {
        assert!(
            ledger.ran[reason] + ledger.reparked[reason] <= ledger.started[reason],
            "a started job leaves the agenda at most once: {}",
            reason.name()
        );
        assert_eq!(
            ledger.requested(reason),
            ledger.started[reason] + ledger.already_pending[reason]
        );
    }
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

#[test]
fn retained_session_work_is_reported_per_request_instead_of_replaying_the_cold_snapshot() {
    let trace = PublicTrace::compile_requests("def main(), do: 1\n", &[None]);
    let requests = CausalReport::derive_requests(trace.events());
    assert_eq!(requests.len(), 2);

    let cold = &requests[0].sessions;
    let unchanged = &requests[1].sessions;
    assert_eq!(unchanged.sessions, 1);
    assert_eq!(unchanged.producer_pokes, 0);
    assert_eq!(unchanged.ledger, WorkLedger::default());

    let run = CausalReport::derive(trace.events());
    assert_eq!(run.sessions.producer_pokes, cold.producer_pokes);
    assert_eq!(run.sessions.ledger, cold.ledger);
}

/// fz-kdt.34's three target fixtures. Chosen by the epic: a convergence-heavy
/// reduce bridge, a predicate search that halts early, and the take/drop/split
/// suite whose 2.6k evaluations make it the widest causal surface in the tree.
const TARGET_FIXTURES: [&str; 3] = [
    "fixtures/00567_fz_f98_range_map_converges.fz",
    "fixtures/00571_enum_predicate_search.fz",
    "fixtures/00420_enum_take_drop_split.fz",
];

const SCENARIOS: [&str; 5] = [
    "cold",
    "unchanged",
    "unreachable_edit",
    "reached_leaf_edit",
    "callee_replaced",
];

// (reachable executables, construction wrappers) per target fixture.
// is unchanged.
const POPULATION_BASELINES: [(u64, u64); 3] = [(48, 0), (190, 32), (185, 38)];

fn target_edit_sequence(fixture: &str) -> (String, [&'static str; 3]) {
    let fixture = std::fs::read_to_string(fixture).unwrap_or_else(|error| panic!("read fixture {fixture}: {error}"));
    let source = fixture.replacen("def main() do", "def main() do\n  kdt_reached()", 1);
    (
        format!(
            "def kdt_unreachable(), do: 0\n\
             def kdt_old_leaf(), do: 1\n\
             def kdt_new_leaf(), do: 2\n\
             def kdt_reached(), do: kdt_old_leaf()\n{source}"
        ),
        [
            "def kdt_unreachable(), do: 99\n",
            "def kdt_old_leaf(), do: 3\n",
            "def kdt_new_leaf(), do: 2\ndef kdt_reached(), do: kdt_new_leaf()\n",
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

fn root_session_requests(trace: &PublicTrace) -> Vec<(u64, u64)> {
    let mut request_open = false;
    let mut session_depth = 0_usize;
    let mut roots = Vec::<(u64, Option<u64>)>::new();
    for event in trace.events() {
        if named(event, &["fz", "compiler2", "backend_request", "started"]) {
            assert!(!request_open);
            request_open = true;
        } else if named(event, &["fz", "compiler2", "backend_request", "finished"]) {
            assert!(request_open && session_depth == 0);
            request_open = false;
        } else if request_open && named(event, &["fz", "compiler2", "pull", "session", "started"]) {
            if session_depth == 0 {
                roots.push((event.metadata["session_id"].as_u64().expect("root session id"), None));
            }
            session_depth += 1;
        } else if request_open
            && session_depth == 1
            && named(event, &["fz", "compiler2", "pull", "product", "requested"])
            && roots.last().is_some_and(|(_, request)| request.is_none())
        {
            roots.last_mut().expect("open root session").1 =
                Some(event.metadata["request_id"].as_u64().expect("root product request id"));
        } else if request_open && named(event, &["fz", "compiler2", "pull", "session", "finished"]) {
            session_depth = session_depth.checked_sub(1).expect("balanced nested session");
        }
    }
    assert!(!request_open && session_depth == 0);
    roots
        .into_iter()
        .map(|(session, request)| (session, request.expect("root session must request a product")))
        .collect()
}

#[test]
fn target_fixture_reports_exercise_all_five_request_scenarios() {
    for (fixture_index, fixture) in TARGET_FIXTURES.into_iter().enumerate() {
        let (source, edits) = target_edit_sequence(fixture);
        let trace = PublicTrace::compile_requests(&source, &[None, Some(edits[0]), Some(edits[1]), Some(edits[2])]);
        let reports = CausalReport::derive_requests(trace.events());
        assert_eq!(reports.len(), SCENARIOS.len(), "{fixture}");
        let root_requests = root_session_requests(&trace);
        assert_eq!(
            root_requests.len(),
            SCENARIOS.len(),
            "{fixture}: one root session per request"
        );
        assert!(
            root_requests.windows(2).all(|pair| pair[0].0 == pair[1].0),
            "{fixture}: request boundaries must reactivate one stable retained root session"
        );
        assert!(
            root_requests.windows(2).all(|pair| pair[0].1 < pair[1].1),
            "{fixture}: one retained session must never reuse a product request identity"
        );
        let cold = reports[0].product_totals();
        let unchanged = reports[1].product_totals();
        assert!(cold.first_productions > 0, "{fixture}: cold population");
        assert_eq!(cold.cross_request_recomputations, 0, "{fixture}: cold request");
        assert_eq!(
            unchanged.evaluations, 0,
            "{fixture}: an unchanged retained root must evaluate no product producers"
        );
        assert_eq!(unchanged.settlements, 0, "{fixture}: unchanged retained settlement");
        assert_eq!(unchanged.retained_cache_hits, 1, "{fixture}: retained root answer");
        assert_eq!(
            unchanged.cross_request_recomputations, 0,
            "{fixture}: retained root answer"
        );
        let irrelevant = reports[2].product_totals();
        assert_eq!(
            irrelevant.evaluations, 0,
            "{fixture}: an unreachable edit must not evaluate a product producer"
        );
        assert_eq!(irrelevant.settlements, 0, "{fixture}: unreachable edit settlement");
        assert_eq!(
            irrelevant.retained_cache_hits, 1,
            "{fixture}: unreachable edit retained answer"
        );
        assert_eq!(irrelevant.displacements, 0, "{fixture}: unreachable edit displacement");
        assert_eq!(
            reports[1].formula_totals().evaluations,
            0,
            "{fixture}: unchanged scheduler work"
        );
        assert_eq!(
            family_work(&reports[2], "DeriveRuntimeDemand").1.evaluations,
            0,
            "{fixture}: an unreachable edit must not evaluate demand formulas"
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
        for (scenario, (name, report)) in SCENARIOS.iter().zip(&reports).enumerate() {
            assert_product_causes_are_exact_or_explicit(fixture, scenario, report);
            let product = report.product_totals();
            let formula = report.formula_totals();
            let (_, runtime_demand) = family_work(report, "DeriveRuntimeDemand");
            // Body walks per fixture per scenario. The cold column carries
            // the whole program, including the arithmetic result/status
            // helpers the reached paths call as ordinary generic functions;
            // the three edit scenarios walk only what their edit moves, which
            // is why `unchanged` and `unreachable_edit` are zero and the two
            // reached edits are a fraction of cold. Tuple-field demands join
            // as prefixes, so a field one consumer reads stays distinct from
            // a field another ignores -- take/drop/split pays two extra cold
            // walks for that and saves eighteen on the replacement edit, which
            // no longer re-walks the bodies a coarsened whole-tuple demand
            // reached. A run missing a callee's answer waits for it rather
            // than guessing; a waiting run only adds to the answers it already
            // gave; and a job whose callee is being derived again waits for
            // that answer before walking. So no body is walked again to revise
            // a guess, and after an edit callees answer before their callers.
            assert_eq!(
                runtime_demand.runtime_demand_evaluations,
                // Executable facts are a pure function of their declared reads, so a reached leaf
                // edit re-derives nothing it did not change and walks exactly the edited body.
                [[109, 0, 0, 1, 4], [442, 0, 0, 1, 4], [466, 0, 0, 1, 4]][fixture_index][scenario],
                "{fixture} {name}: count actual body walks, not scheduler completions; all scenarios: {:?}",
                reports
                    .iter()
                    .map(|report| family_work(report, "DeriveRuntimeDemand").1.runtime_demand_evaluations)
                    .collect::<Vec<_>>()
            );
            assert_eq!(
                runtime_demand.uncaused, 0,
                "{fixture} {name}: every non-initial RuntimeDemand evaluation must name moved content; uncaused={:?}",
                report.uncaused,
            );
            assert_eq!(
                runtime_demand.readiness_caused, 0,
                "{fixture} {name}: readiness-only movement must not evaluate RuntimeDemand"
            );
            assert_eq!(
                runtime_demand.evaluations,
                runtime_demand.initial + runtime_demand.content_caused + runtime_demand.concluded_caused,
                "{fixture} {name}: RuntimeDemand work must be initial, content-caused, or caused by an answer it waited on concluding"
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
            assert_eq!(
                report.sessions.ledger.ran.unsanctioned_work_starts(),
                0,
                "{fixture} {name}"
            );
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
        totals.add(work);
    }
    (formulas, totals)
}

/// fz-kdt.56's ratchet, per target fixture: `(DeriveCallGraphComponent
/// evaluations, evaluations that concluded nothing)`.
///
/// The component walk publishes the function's strong-component id alongside the body
/// keying that component decides, so one walk answers both questions.
/// Per fixture: DeriveCallGraphComponent (evaluations, concluded-nothing), then
/// DeriveStaticCallees (evaluations, blocked). The blocked completions are the pull's own
/// layered discovery of the edge facts, which no formulation avoids: a cone cannot be known
/// before it is walked.
///
/// The last column of each row is the `DeriveStaticReach` evaluations: the walks that answer
/// each function's recursion from the edge facts, one fact per function whose recursion is asked.
const DERIVE_RECURSIVE_RATCHET: [(&str, u64, u64, u64, u64, u64); 7] = [
    // The ordering operators end in an `any`/`any` clause through `compare/2`; this
    // fixture's operands stay numeric, so no `compare/2` activation is minted and the
    // StaticCallees count covers only the numeric families' callee layers.
    ("fixtures/00567_fz_f98_range_map_converges.fz", 21, 0, 65, 0, 35),
    ("fixtures/00571_enum_predicate_search.fz", 34, 0, 49, 0, 64),
    ("fixtures/00420_enum_take_drop_split.fz", 55, 0, 113, 0, 97),
    // 00607-00610 pin the shared-reach shape directly. Four callers (p1-p4)
    // share one call chain of depth eight. Each caller's reach walks the chain's
    // edge facts itself and reads no other reach, so the work is the same
    // whichever order the source defines callers and callees in.
    // A recursion verdict starts once its reach exists, so none concludes nothing.
    (
        "fixtures/00607_static_reach_shared_chain_callees_first.fz",
        13,
        0,
        18,
        0,
        21,
    ),
    (
        "fixtures/00608_static_reach_shared_chain_callers_first.fz",
        13,
        0,
        18,
        0,
        21,
    ),
    (
        "fixtures/00609_static_reach_chain_into_recursion_callees_first.fz",
        15,
        0,
        25,
        0,
        23,
    ),
    (
        "fixtures/00610_static_reach_chain_into_recursion_callers_first.fz",
        15,
        0,
        25,
        0,
        23,
    ),
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
    for (fixture, evaluations, concluded_nothing, callee_evaluations, callee_blocked, reach_evaluations) in
        DERIVE_RECURSIVE_RATCHET
    {
        let trace = compile_fixture(fixture);
        assert!(
            matches!(trace.outcome, DriveOutcome::Resolved),
            "{fixture} must resolve for its causal report to describe a whole compile"
        );
        let report = CausalReport::derive(trace.events());

        let (_, recursive) = family_work(&report, "DeriveRecursive");
        assert_eq!(
            (recursive.evaluations, recursive.unchanged_outputs),
            (evaluations, concluded_nothing),
            "{fixture}: DeriveRecursive work moved off its fz-kdt.56 pin; re-measure \
             and re-pin with the reason. Full row: {recursive:?}"
        );

        let (_, reach) = family_work(&report, "DeriveStaticReach");
        assert_eq!(
            reach.evaluations, reach_evaluations,
            "{fixture}: DeriveStaticReach work moved off its pin. Full row: {reach:?}"
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

/// Per target fixture: the analysis's claim lifecycles, shift work and evaluation counts
/// over a whole compile.
const ANALYSIS_CLAIM_RATCHET: [AnalysisClaimRatchet; 3] = [
    AnalysisClaimRatchet {
        fixture: "fixtures/00567_fz_f98_range_map_converges.fz",
        activations: lifecycle(55, 55, 0),
        callsites: lifecycle(59, 59, 0),
        shifts: shifts(4, 12),
        analyze_evaluations: 153,
        analyze_zero_change: 5,
        // Macro readiness is a retained content dependency.
        total_evaluations: 718,
    },
    AnalysisClaimRatchet {
        fixture: "fixtures/00571_enum_predicate_search.fz",
        activations: lifecycle(195, 195, 0),
        callsites: lifecycle(248, 248, 0),
        shifts: shifts(25, 75),
        analyze_evaluations: 593,
        analyze_zero_change: 25,
        total_evaluations: 1210,
    },
    AnalysisClaimRatchet {
        fixture: "fixtures/00420_enum_take_drop_split.fz",
        activations: lifecycle(223, 223, 0),
        callsites: lifecycle(384, 384, 0),
        shifts: shifts(44, 91),
        analyze_evaluations: 663,
        analyze_zero_change: 23,
        total_evaluations: 1658,
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
            (7, 7, 7),
            "{fixture}: the total is the World fact producers that replaced the product formula: \
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
        let (_, runtime_demand_work) = family_work(&report, "DeriveRuntimeDemand");
        assert_eq!(
            report.formula_totals().evaluations - runtime_demand_work.evaluations,
            total_evaluations,
            "{fixture}: semantic formula work must remain at its measured count"
        );
        assert_eq!(
            runtime_demand_work.uncaused, 0,
            "{fixture}: every non-initial RuntimeDemand evaluation must name its exact cause"
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
/// `main` reaches the call while `M.helper/2` has neither its contract nor
/// the facts that key its activation. `junk` is an unused list parameter
/// threaded through unread: carrying a list keeps the row off R1's
/// self-keyed shortcut (a ground int argument alone answers its own
/// `Recursive`/`InputDemand` with no fact asked at all), so this call
/// genuinely asks for them.
const CONTRACT_CALLEE_SOURCE: &str = "defmodule M do\n  @spec helper(integer, [integer]) :: integer\n  def helper(x, junk), do: x + 1\nend\ndef main(), do: M.helper(41, [1])\n";

/// The function-keyed facts a completion reports itself blocked on, as
/// `"Kind(function_id)"` — kind plus `function_id` is the whole identity the
/// public stream renders for `FunctionContract`/`Recursive`/`InputDemand`.
fn blocked_function_facts(completion: &serde_json::Value) -> crate::fast_hash::HashSet<String> {
    let Some(blocked) = completion.get("blocked").and_then(|v| v.as_array()) else {
        return crate::fast_hash::HashSet::default();
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
/// Before a call to `M.helper/2` can resolve, the callee's contract must be
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

    let helper = function_id_named(&trace, "M.helper/2");
    let prerequisites = ["FunctionContract", "Recursive", "InputDemand"]
        .into_iter()
        .map(|kind| format!("{kind}({helper})"))
        .collect::<crate::fast_hash::HashSet<_>>();

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
        "an analysis must spend exactly ONE block on M.helper/2's prerequisites; \
         each extra block is a rung of a ladder. Blocks seen: {blocks:?}"
    );
    assert!(
        blocks[0].is_superset(&prerequisites),
        "the single block must name the contract AND both keying facts together, \
         so one wake satisfies them all. Named: {:?}, required: {prerequisites:?}",
        blocks[0]
    );
}
