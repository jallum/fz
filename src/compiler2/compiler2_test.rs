use super::{CodeSubmission, Compiler2, Job};
use crate::telemetry::capture::OwnedEvent;
use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Value};

struct ContractCase<'a> {
    name: &'a str,
    source_name: &'a str,
    source_text: &'a str,
}

#[test]
fn compiler2_contract_harness_keeps_code_ingest_isolated_from_production_compiler() {
    for case in [
        ContractCase {
            name: "inline_main",
            source_name: "inline_main.fz",
            source_text: "fn main(), do: 42\n",
        },
        ContractCase {
            name: "fixture_add1",
            source_name: "fixtures/add1/input.fz",
            source_text: include_str!("../../fixtures/add1/input.fz"),
        },
    ] {
        run_contract(case);
    }
}

fn run_contract(case: ContractCase<'_>) {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut compiler = Compiler2::new(&tel);

    let code_id = compiler.submit_code(CodeSubmission {
        name: Some(case.source_name.to_string()),
        text: case.source_text.to_string(),
    });

    let submitted_event = capture
        .last(&["fz", "compiler2", "code", "submitted"])
        .expect("compiler2 submitted event");
    let submitted_id = match submitted_event.measurements.get("code_id") {
        Some(Value::U64(id)) => *id,
        other => panic!("submitted event missing code_id measurement: {other:?}"),
    };
    assert_eq!(
        submitted_id,
        code_id.as_u32() as u64,
        "{} should report the submitted code id",
        case.name
    );
    let submitted_name = match submitted_event.metadata.get("name") {
        Some(Value::Str(name)) => name.as_ref(),
        other => panic!("submitted event missing name metadata: {other:?}"),
    };
    assert_eq!(
        submitted_name, case.source_name,
        "{} should report the source name",
        case.name
    );
    let submitted_bytes = match submitted_event.measurements.get("bytes") {
        Some(Value::U64(bytes)) => *bytes,
        other => panic!("submitted event missing bytes measurement: {other:?}"),
    };
    assert_eq!(
        submitted_bytes,
        case.source_text.len() as u64,
        "{} should report the submitted byte length",
        case.name
    );

    assert_eq!(
        job_stops(&capture, "IndexCode").len(),
        0,
        "{} should not index before drive runs",
        case.name
    );

    compiler
        .drive()
        .expect("compiler2 drive should index the submitted code");

    let drive_span = capture
        .find(&["fz", "compiler2", "drive"])
        .into_iter()
        .find(|event| event.kind == EventKind::SpanStart)
        .expect("compiler2 drive span start");
    let pending_jobs = match drive_span.metadata.get("pending_jobs") {
        Some(Value::U64(count)) => *count,
        other => panic!("drive span missing pending_jobs metadata: {other:?}"),
    };
    assert_eq!(
        pending_jobs, 1,
        "{} should start drive with one pending indexing job",
        case.name
    );
    let drive_stop = capture
        .find(&["fz", "compiler2", "drive"])
        .into_iter()
        .find(|event| event.kind == EventKind::SpanStop)
        .expect("compiler2 drive span stop");
    let jobs_ran = match drive_stop.measurements.get("jobs_ran") {
        Some(Value::U64(count)) => *count,
        other => panic!("drive stop missing jobs_ran measurement: {other:?}"),
    };
    let expected_jobs = 1;
    assert_eq!(
        jobs_ran, expected_jobs,
        "{} should only process the index job without explicit demand",
        case.name
    );
    let drive_outcome = match drive_stop.metadata.get("outcome") {
        Some(Value::Str(value)) => value.as_ref(),
        other => panic!("drive stop missing outcome metadata: {other:?}"),
    };
    assert_eq!(drive_outcome, "ok", "{} should close drive with ok outcome", case.name);

    let indexed_start = job_start(&capture, "IndexCode", code_id.as_u32() as u64);
    assert_eq!(
        indexed_start.parent_span_id, drive_span.span_id,
        "{} should start indexed work under the drive span",
        case.name
    );
    let indexed_stop = job_stop(&capture, &indexed_start);
    assert_eq!(
        indexed_stop.parent_span_id, drive_span.span_id,
        "{} should emit indexed work under the drive span",
        case.name
    );
    assert_eq!(
        metadata_str(&indexed_stop, "outcome"),
        "ok",
        "{} should close the indexing job with ok outcome",
        case.name
    );

    assert_eq!(
        capture.count(&["fz", "compiler2", "function", "defined"]),
        0,
        "{} should not define functions without explicit demand",
        case.name
    );

    assert_eq!(
        capture.count(&["fz", "compiler2", "module", "defined"]),
        0,
        "{} should not define modules without explicit demand",
        case.name
    );
    assert_eq!(
        job_stops(&capture, "IndexCode").len(),
        1,
        "{} should close exactly one IndexCode job span",
        case.name
    );
    assert_eq!(
        capture
            .last(&["fz", "compiler2", "job"])
            .map(|event| event.kind)
            .unwrap_or(EventKind::Event),
        EventKind::SpanStop,
        "{} should finish with the job stop event after the first drive",
        case.name
    );
    assert!(
        indexed_stop.metadata.get("effects").is_none(),
        "{} capture should not durable-copy opaque job effects",
        case.name
    );
    assert_eq!(
        capture.find(&["fz", "compiler2", "module", "defined"]).len(),
        0,
        "{} should not emit module.defined during discovery-only drive",
        case.name
    );
    assert_eq!(
        capture.find(&["fz", "compiler2", "function", "defined"]).len(),
        0,
        "{} should not emit function.defined during discovery-only drive",
        case.name
    );
    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "{} should not invoke the production frontend",
        case.name
    );
    assert_eq!(
        capture.count(&["fz", "planner", "planned"]),
        0,
        "{} should not invoke the production planner",
        case.name
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "code", "submitted"]),
        1,
        "{} should emit exactly one Compiler2 submission event",
        case.name
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "code", "indexed"]),
        0,
        "{} should not emit a separate Compiler2 indexed event",
        case.name
    );
    assert_eq!(
        job_stops(&capture, "IndexCode").len(),
        1,
        "{} should close exactly one IndexCode job span",
        case.name
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "fact", "published"]),
        0,
        "{} should not emit redundant fact.published telemetry",
        case.name
    );

    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "{} should accept an explicit define-code demand after indexing",
        case.name
    );
}

fn job_start(capture: &Capture, job_kind: &str, id: u64) -> OwnedEvent {
    capture
        .find(&["fz", "compiler2", "job"])
        .into_iter()
        .find(|event| {
            event.kind == EventKind::SpanStart
                && matches!(event.metadata.get("kind"), Some(Value::Str(kind)) if kind.as_ref() == job_kind)
                && matches!(event.metadata.get("id"), Some(Value::U64(value)) if *value == id)
        })
        .unwrap_or_else(|| panic!("{job_kind} job start event for id {id}"))
}

fn job_stop(capture: &Capture, start: &OwnedEvent) -> OwnedEvent {
    capture
        .find(&["fz", "compiler2", "job"])
        .into_iter()
        .find(|event| event.kind == EventKind::SpanStop && event.span_id == start.span_id)
        .unwrap_or_else(|| panic!("job stop event for span {}", start.span_id))
}

fn job_stops(capture: &Capture, job_kind: &str) -> Vec<OwnedEvent> {
    capture
        .find(&["fz", "compiler2", "job"])
        .into_iter()
        .filter(|event| {
            event.kind == EventKind::SpanStart
                && matches!(event.metadata.get("kind"), Some(Value::Str(kind)) if kind.as_ref() == job_kind)
        })
        .filter_map(|start| {
            capture
                .find(&["fz", "compiler2", "job"])
                .into_iter()
                .find(|event| event.kind == EventKind::SpanStop && event.span_id == start.span_id)
        })
        .collect()
}

fn metadata_str<'a>(event: &'a OwnedEvent, key: &str) -> &'a str {
    match event.metadata.get(key) {
        Some(Value::Str(value)) => value.as_ref(),
        other => panic!("metadata key `{key}` missing or not str: {other:?}"),
    }
}
