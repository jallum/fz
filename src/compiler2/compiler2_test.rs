use super::{CodeSubmission, Compiler2, DriveOutcome, Job};
use crate::telemetry::handler::{Event, Handler};
use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Value};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

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
    let jobs = JobCapture::new();
    tel.attach(&["fz", "compiler2", "job"], jobs.handler());
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
    assert_eq!(
        submitted_event.metadata.len(),
        0,
        "{} should not durable-capture synthesized code submission metadata",
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
        jobs.stop_count(Job::IndexCode(code_id)),
        0,
        "{} should not index before drive runs",
        case.name
    );

    assert!(
        matches!(compiler.drive(), DriveOutcome::Resolved),
        "compiler2 drive should index the submitted code and finish resolved"
    );

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
    assert_eq!(
        drive_stop.metadata.len(),
        0,
        "{} should not durable-capture resolved drive metadata",
        case.name
    );
    let indexed_start = jobs.start(Job::IndexCode(code_id));
    assert_eq!(
        indexed_start.parent_span_id, drive_span.span_id,
        "{} should start indexed work under the drive span",
        case.name
    );
    let indexed_stop = jobs.stop(Job::IndexCode(code_id));
    assert_eq!(
        indexed_stop.parent_span_id, drive_span.span_id,
        "{} should emit indexed work under the drive span",
        case.name
    );
    assert!(
        indexed_stop.effects_present,
        "{} should close the indexing job with effects metadata",
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
        jobs.stop_count(Job::IndexCode(code_id)),
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
        capture
            .find(&["fz", "compiler2", "job"])
            .into_iter()
            .filter(|event| event.kind == EventKind::SpanStop && event.span_id == indexed_stop.span_id)
            .all(|event| event.metadata.get("effects").is_none()),
        "{} generic capture should not durable-copy opaque job effects",
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
        jobs.stop_count(Job::IndexCode(code_id)),
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

#[derive(Debug, Clone)]
struct JobSpanStart {
    job: Job,
    parent_span_id: u64,
}

#[derive(Debug, Clone)]
struct JobSpanStop {
    job: Job,
    span_id: u64,
    parent_span_id: u64,
    effects_present: bool,
}

struct JobCapture {
    live: Rc<RefCell<HashMap<u64, Job>>>,
    starts: Rc<RefCell<Vec<JobSpanStart>>>,
    stops: Rc<RefCell<Vec<JobSpanStop>>>,
}

impl JobCapture {
    fn new() -> Self {
        Self {
            live: Rc::new(RefCell::new(HashMap::new())),
            starts: Rc::new(RefCell::new(Vec::new())),
            stops: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(JobCaptureHandler {
            live: self.live.clone(),
            starts: self.starts.clone(),
            stops: self.stops.clone(),
        })
    }

    fn start(&self, job: Job) -> JobSpanStart {
        self.starts
            .borrow()
            .iter()
            .find(|start| start.job == job)
            .cloned()
            .unwrap_or_else(|| panic!("job start event for {job:?}"))
    }

    fn stop(&self, job: Job) -> JobSpanStop {
        self.stops
            .borrow()
            .iter()
            .find(|stop| stop.job == job)
            .cloned()
            .unwrap_or_else(|| panic!("job stop event for {job:?}"))
    }

    fn stop_count(&self, job: Job) -> usize {
        self.stops.borrow().iter().filter(|stop| stop.job == job).count()
    }
}

struct JobCaptureHandler {
    live: Rc<RefCell<HashMap<u64, Job>>>,
    starts: Rc<RefCell<Vec<JobSpanStart>>>,
    stops: Rc<RefCell<Vec<JobSpanStop>>>,
}

impl Handler for JobCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "job"] {
            return;
        }
        match event.kind {
            EventKind::SpanStart => {
                let Some(job) = event.metadata.get("job").and_then(|value| value.downcast_ref::<Job>()) else {
                    return;
                };
                self.live.borrow_mut().insert(event.span_id, job.clone());
                self.starts.borrow_mut().push(JobSpanStart {
                    job: job.clone(),
                    parent_span_id: event.parent_span_id,
                });
            }
            EventKind::SpanStop => {
                let Some(job) = self.live.borrow_mut().remove(&event.span_id) else {
                    return;
                };
                self.stops.borrow_mut().push(JobSpanStop {
                    job,
                    span_id: event.span_id,
                    parent_span_id: event.parent_span_id,
                    effects_present: event.metadata.get("effects").is_some(),
                });
            }
            EventKind::Event | EventKind::SpanException => {}
        }
    }
}
