use super::{CodeSubmission, Compiler2, DriveOutcome, Job};
use crate::exec::runtime::DbgCapture;
use crate::ir_interp::{
    tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset, tests_support_lock,
};
use crate::telemetry::handler::{Event, Handler};
use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind, Value};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;

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
            source_text: include_str!("../../fixtures2/00009_no_runtime.fz"),
        },
        ContractCase {
            name: "fixture_add1",
            source_name: "fixtures2/behavior/add1.fz",
            source_text: include_str!("../../fixtures2/behavior/add1.fz"),
        },
    ] {
        run_contract(case);
    }
}

#[test]
fn compiler2_root_drive_timeout_reports_the_configured_limit() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.set_drive_timeout(Duration::ZERO);
    compiler.submit_code(CodeSubmission {
        name: Some("timeout_main.fz".to_string()),
        text: "fn main(), do: 0\n".to_string(),
    });
    let root = compiler.submit_root(super::RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: super::ExecutableNeed::Value,
    });

    let error = compiler
        .run_root_interp(root)
        .expect_err("zero drive timeout should abort before compiler work runs");
    assert!(
        error.contains("exceeded 0 ms drive limit after 0 jobs"),
        "timeout should report the configured compiler drive limit, got: {error}"
    );
}

#[test]
fn compiler2_drive_honors_the_configured_timeout() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(&tel);
    compiler.set_drive_timeout(Duration::ZERO);
    compiler.submit_code(CodeSubmission {
        name: Some("timeout_drive.fz".to_string()),
        text: "fn main(), do: 0\n".to_string(),
    });

    let outcome = compiler.drive();
    assert!(
        matches!(
            outcome,
            DriveOutcome::TimedOut {
                jobs_ran: 0,
                pending_jobs: 1
            }
        ),
        "compiler.drive() should honor the configured timeout, got: {outcome:?}"
    );
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

fn assert_no_legacy_planner_or_type_infer(capture: &Capture, context: &str) {
    assert!(
        capture.find(&["fz", "type_infer"]).is_empty() && capture.find(&["fz", "planner"]).is_empty(),
        "{context}",
    );
}

fn assert_native_backend_compile_span(capture: &Capture, backend: &str, context: &str) {
    let starts = |name: &[&str]| {
        capture
            .find(name)
            .into_iter()
            .filter(|event| event.kind == EventKind::SpanStart)
            .collect::<Vec<_>>()
    };
    let stops = |name: &[&str]| {
        capture
            .find(name)
            .into_iter()
            .filter(|event| event.kind == EventKind::SpanStop)
            .collect::<Vec<_>>()
    };

    let boundary_starts = starts(&["fz", "compiler2", "native_backend", "compile"]);
    assert_eq!(
        boundary_starts.len(),
        1,
        "{context}: compiler2 should name the native backend boundary once"
    );
    let boundary = &boundary_starts[0];
    match boundary.metadata.get("backend") {
        Some(Value::Str(actual)) => assert_eq!(actual.as_ref(), backend, "{context}: backend metadata"),
        other => panic!("{context}: native backend span missing backend metadata: {other:?}"),
    }
    for key in [
        "root_id",
        "backend_revision",
        "entry_fn_id",
        "body_count",
        "callable_entry_count",
    ] {
        assert!(
            matches!(boundary.metadata.get(key), Some(Value::U64(_))),
            "{context}: native backend span should carry numeric `{key}` metadata"
        );
    }

    let boundary_stops = stops(&["fz", "compiler2", "native_backend", "compile"]);
    assert_eq!(
        boundary_stops.len(),
        1,
        "{context}: compiler2 native backend span should close once"
    );
    assert_eq!(
        boundary_stops[0].span_id, boundary.span_id,
        "{context}: native backend start/stop should share one span id"
    );

    let codegen_compile = starts(&["fz", "codegen", "compile"]);
    assert_eq!(
        codegen_compile.len(),
        1,
        "{context}: codegen should emit one compile span"
    );
    assert_eq!(
        codegen_compile[0].parent_span_id, boundary.span_id,
        "{context}: codegen compile should nest under the compiler2 native backend boundary"
    );
}

struct NativeEntryCase<'a> {
    name: &'a str,
    source_name: &'a str,
    source_text: String,
    root_name: &'a str,
    expected_halt: i64,
    expected_dbg: Option<&'a str>,
}

#[test]
fn compiler2_compile_root_jit_consumes_native_program_without_legacy_prepare() {
    let quicksort = include_str!("../../fixtures2/00020_quicksort_jit_entry.fz").to_string();
    let cases = [
        NativeEntryCase {
            name: "quicksort",
            source_name: "fixtures/quicksort_compiler2_jit.fz",
            source_text: quicksort,
            root_name: "entry",
            expected_halt: 42,
            expected_dbg: Some("[1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9]"),
        },
        NativeEntryCase {
            name: "enum_reduce",
            source_name: "fixtures/enum_reduce_compiler2_jit.fz",
            source_text: include_str!("../../fixtures2/00010_enum_reduce_main.fz").to_string(),
            root_name: "main",
            expected_halt: 15,
            expected_dbg: None,
        },
        NativeEntryCase {
            name: "variadic_extern",
            source_name: "fixtures/variadic_open_compiler2_jit.fz",
            source_text: include_str!("../../fixtures2/00015_variadic_open_jit.fz").to_string(),
            root_name: "main",
            expected_halt: -1,
            expected_dbg: None,
        },
    ];

    for case in cases {
        let tel = ConfiguredTelemetry::new();
        let capture = Capture::new();
        tel.attach(&[], capture.handler());
        let dbg = DbgCapture::new();
        tel.attach(&[], dbg.handler());
        let mut compiler = Compiler2::new(&tel);
        compiler.submit_code(CodeSubmission {
            name: Some(case.source_name.to_string()),
            text: case.source_text,
        });
        let root_id = compiler.submit_root(super::RootSubmission {
            module_name: None,
            name: case.root_name.to_string(),
            arity: 0,
            need: super::ExecutableNeed::Value,
        });

        let (compiled, entry) = compiler
            .compile_root_jit(root_id)
            .unwrap_or_else(|err| panic!("{} should JIT-compile through NativeProgram: {err}", case.name));
        assert_native_backend_compile_span(&capture, "jit", case.name);
        assert_eq!(
            compiled.run(&tel, entry),
            case.expected_halt,
            "{} should preserve the Compiler2-native JIT result",
            case.name
        );
        if let Some(expected_dbg) = case.expected_dbg {
            assert_eq!(
                dbg.lines().first().map(String::as_str),
                Some(expected_dbg),
                "{} should preserve dbg output through the Compiler2 JIT front door",
                case.name
            );
        }
        assert_no_legacy_planner_or_type_infer(
            &capture,
            "Compiler2 JIT front door should not reopen legacy planning or type inference",
        );
    }
}

#[test]
fn compiler2_compile_root_aot_consumes_native_program_without_legacy_prepare() {
    let cases = [
        (
            "quicksort",
            "fixtures/quicksort_compiler2_aot.fz",
            include_str!("../../fixtures2/behavior/quicksort.fz").to_string(),
            "quicksort_compiler2",
        ),
        (
            "enum_reduce",
            "fixtures/enum_reduce_compiler2_aot.fz",
            include_str!("../../fixtures2/00010_enum_reduce_main.fz").to_string(),
            "enum_reduce_compiler2",
        ),
        (
            "variadic_extern",
            "fixtures/variadic_open_compiler2_aot.fz",
            include_str!("../../fixtures2/00015_variadic_open_jit.fz").to_string(),
            "variadic_open_compiler2",
        ),
    ];

    for (name, source_name, source_text, obj_name) in cases {
        let tel = ConfiguredTelemetry::new();
        let capture = Capture::new();
        tel.attach(&[], capture.handler());
        let mut compiler = Compiler2::new(&tel);
        compiler.submit_code(CodeSubmission {
            name: Some(source_name.to_string()),
            text: source_text,
        });
        let root_id = compiler.submit_root(super::RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: super::ExecutableNeed::Value,
        });

        let artifact = compiler
            .compile_root_aot(root_id, obj_name)
            .unwrap_or_else(|err| panic!("{name} should AOT-compile through NativeProgram: {err}"));
        assert_native_backend_compile_span(&capture, "aot", name);
        assert!(
            !artifact.object.is_empty(),
            "{name} should produce a non-empty AOT object through the Compiler2 front door",
        );
        assert_eq!(
            artifact.main_symbol.as_deref(),
            Some("main"),
            "{name} should preserve the C-callable main symbol through the Compiler2 AOT front door",
        );
        assert_no_legacy_planner_or_type_infer(
            &capture,
            "Compiler2 AOT front door should not reopen legacy planning or type inference",
        );
    }
}

#[test]
fn compiler2_run_root_jit_executes_resources_without_legacy_prepare() {
    let _lock = tests_support_lock().lock().unwrap();
    tests_support_dtor_reset();

    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/compiler2_run_root_jit_resource.fz".to_string()),
        text: include_str!("../../fixtures2/00026_make_resource.fz").to_string(),
    });
    let root_id = compiler.submit_root(super::RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: super::ExecutableNeed::Value,
    });

    compiler
        .run_root_jit(root_id)
        .unwrap_or_else(|error| panic!("resource fixture should run through Compiler2 JIT: {error}"));
    assert_native_backend_compile_span(&capture, "jit", "Compiler2 run_root_jit");

    assert_eq!(
        tests_support_dtor_fired(),
        1,
        "Compiler2 JIT run should drain exactly one resource destructor",
    );
    assert_eq!(
        tests_support_dtor_last_payload(),
        42,
        "Compiler2 JIT run should pass the resource payload into the destructor body",
    );
    assert!(
        capture.find(&["fz", "runtime", "dtor_drain_failed"]).is_empty(),
        "Compiler2 JIT run should complete the runtime destructor drain cleanly",
    );
    assert_no_legacy_planner_or_type_infer(
        &capture,
        "Compiler2 JIT run should not reopen the legacy planner or type inference",
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
