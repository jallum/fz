use super::{CodeId, CodeSubmission, Compiler2, DriveOutcome, Job, ModuleInterface, World};
use crate::exec::runtime::DbgCapture;
use crate::ir_interp::{
    tests_support_dtor_fired, tests_support_dtor_last_payload, tests_support_dtor_reset, tests_support_lock,
};
use crate::telemetry::{Capture, ConfiguredTelemetry, EventKind};
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::time::Duration;

struct ContractCase<'a> {
    name: &'a str,
    source_name: &'a str,
    source_text: &'a str,
}

#[test]
fn compiler2_can_own_configured_telemetry() {
    fn requires_owned_configured_telemetry(_: Compiler2<ConfiguredTelemetry>) {}

    requires_owned_configured_telemetry(Compiler2::new(ConfiguredTelemetry::new()));
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
    let mut compiler = Compiler2::new(tel);
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
    let mut compiler = Compiler2::new(tel);
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

// Ported from `world_test`'s interface-only-module coverage, through the
// public `Compiler2` front door instead of poking `World` directly: an
// embedder that owns another module's interface out-of-band (a host module,
// or a sibling compilation unit it does not want to hand this compiler's
// source for) registers that interface here so imports against it resolve
// without ever supplying a body.
#[test]
fn compiler2_submit_module_interface_settles_an_external_module_without_a_body() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    let module = compiler.submit_module_interface("ExternalHost".to_string(), ModuleInterface::default());

    assert!(
        matches!(compiler.drive(), DriveOutcome::Resolved),
        "publishing an interface-only module through Compiler2 should settle without a source body",
    );
    assert!(
        compiler.world().module_defined_revision(module).is_none(),
        "an externally-submitted interface must never gain a body definition on its own",
    );
    assert!(
        compiler.world().module_interface_revision(module).is_some(),
        "Compiler2::submit_module_interface should publish the interface fact the same way World's does",
    );
}

fn run_contract(case: ContractCase<'_>) {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let drive_span_id = Rc::new(Cell::new(0));
    let drive_start = Rc::clone(&drive_span_id);
    let drive_outcome = Rc::new(RefCell::new(None));
    let outcome_sink = Rc::clone(&drive_outcome);
    tel.attach_raw_span0_1::<DriveOutcome<Job, super::drive::DependencyKey>, _, _, _>(
        &["fz", "compiler2", "drive"],
        move |_, span_id, _| drive_start.set(span_id),
        move |_, _, _, _, outcome| *outcome_sink.borrow_mut() = Some(outcome.clone()),
        |_, _, _, _| {},
    );
    let submissions = Rc::new(RefCell::new(Vec::<(CodeId, usize)>::new()));
    let submission_sink = Rc::clone(&submissions);
    tel.attach_raw_event2::<World, CodeId, _>(
        &["fz", "compiler2", "code", "submitted"],
        move |_, _, _, world, code| {
            submission_sink.borrow_mut().push((*code, world.code_text(*code).len()));
        },
    );
    let jobs = JobCapture::new();
    jobs.install(&tel);
    let mut compiler = Compiler2::new(tel);

    let code_id = compiler.submit_code(CodeSubmission {
        name: Some(case.source_name.to_string()),
        text: case.source_text.to_string(),
    });

    let submitted = submissions.borrow();
    let (submitted_id, submitted_bytes) = *submitted.last().expect("compiler2 submitted event");
    assert_eq!(
        submitted_id, code_id,
        "{} should report the submitted code id",
        case.name
    );
    assert_eq!(
        submitted_bytes,
        case.source_text.len(),
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

    assert!(matches!(*drive_outcome.borrow(), Some(DriveOutcome::Resolved)));
    let indexed_start = jobs.start(Job::IndexCode(code_id));
    assert_eq!(
        indexed_start.parent_span_id,
        drive_span_id.get(),
        "{} should start indexed work under the drive span",
        case.name
    );
    let indexed_stop = jobs.stop(Job::IndexCode(code_id));
    assert_eq!(
        indexed_stop.parent_span_id,
        drive_span_id.get(),
        "{} should emit indexed work under the drive span",
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
        submissions.borrow().len(),
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

fn assert_native_backend_compile_span(capture: &Capture, context: &str) {
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
        capture.install(&tel, &[]);
        let dbg = DbgCapture::new();
        let mut compiler = Compiler2::new(tel);
        compiler.set_output(dbg.sink());
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
        assert_native_backend_compile_span(&capture, case.name);
        assert_eq!(
            compiled.run_with_output(compiler.telemetry(), &dbg, entry),
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
        capture.install(&tel, &[]);
        let mut compiler = Compiler2::new(tel);
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
        assert_native_backend_compile_span(&capture, name);
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
fn compiler2_native_front_doors_jit_and_aot_enum_reduce_through_the_product_path() {
    // enum_reduce exercises a callable boundary (Enum.reduce takes a closure).
    // The JIT and AOT front doors reach the BackendProgram through the same
    // product driver as interp (`build_backend_product`).
    let source = include_str!("../../fixtures2/00010_enum_reduce_main.fz");

    // JIT front door.
    {
        let tel = ConfiguredTelemetry::new();
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures/enum_reduce_native_front_door_jit.fz".to_string()),
            text: source.to_string(),
        });
        let root = compiler.submit_root(super::RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: super::ExecutableNeed::Value,
        });
        let (compiled, entry) = compiler
            .compile_root_jit(root)
            .expect("enum_reduce should JIT-compile through the product path");
        assert_eq!(
            compiled.run(compiler.telemetry(), entry),
            15,
            "enum_reduce should preserve its JIT result through the native front door",
        );
    }

    // AOT front door.
    {
        let tel = ConfiguredTelemetry::new();
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures/enum_reduce_native_front_door_aot.fz".to_string()),
            text: source.to_string(),
        });
        let root = compiler.submit_root(super::RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: super::ExecutableNeed::Value,
        });
        let artifact = compiler
            .compile_root_aot(root, "enum_reduce_native_front_door")
            .expect("enum_reduce should AOT-compile through the product path");
        assert!(
            !artifact.object.is_empty(),
            "enum_reduce should produce a non-empty AOT object through the native front door",
        );
    }
}

#[test]
fn compiler2_run_root_jit_executes_resources_without_legacy_prepare() {
    let _lock = tests_support_lock().lock().unwrap();
    tests_support_dtor_reset();

    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);

    let mut compiler = Compiler2::new(tel);
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
    assert_native_backend_compile_span(&capture, "Compiler2 run_root_jit");

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

/// Overproduction guard: an interp drive demands only `BackendProgram`, so it
/// must never lower a `NativeProgram` no consumer asked for -- the spreadsheet-
/// model rule (produce only what the demander needs). The JIT and AOT front
/// doors demand the exact `NativeProgram(root)` product, so they must still
/// produce it.
///
/// This counts the one telemetry event
/// `lower_native_program` unconditionally emits per successful lowering
/// (`["fz","compiler2","native_program","reusable_cons"]`) instead of tapping
/// that span.
#[test]
fn compiler2_interp_never_lowers_native_program_while_jit_and_aot_still_do() {
    let source = include_str!("../../fixtures2/00181_enum_reduce_operator_ref.fz");

    // Interp front door: BackendProgram only, NativeProgram absent.
    {
        let tel = ConfiguredTelemetry::new();
        let lowered = capture_native_lowerings(&tel);
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures/interp_never_lowers_native.fz".to_string()),
            text: source.to_string(),
        });
        let root = compiler.submit_root(super::RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: super::ExecutableNeed::Value,
        });

        compiler
            .run_root_interp(root)
            .unwrap_or_else(|error| panic!("enum_reduce_operator_ref should interp-run: {error}"));

        assert_eq!(
            lowered.get(),
            0,
            "an interp drive must never lower NativeProgram -- interp reads BackendProgram, \
             never NativeProgram, so lowering native off the backend product is pure overproduction",
        );
        assert_eq!(
            compiler.retained_product_generation(root, &super::ProductKey::NativeProgram(root)),
            None
        );
    }

    // JIT front door: NativeProgram still produced, through one explicit demand.
    {
        let tel = ConfiguredTelemetry::new();
        let lowered = capture_native_lowerings(&tel);
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures/jit_still_lowers_native.fz".to_string()),
            text: source.to_string(),
        });
        let root = compiler.submit_root(super::RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: super::ExecutableNeed::Value,
        });

        compiler
            .compile_root_jit(root)
            .unwrap_or_else(|error| panic!("enum_reduce_operator_ref should JIT-compile: {error}"));

        assert_eq!(
            lowered.get(),
            1,
            "the JIT front door demands NativeProgram exactly once through compile_root_jit",
        );
        assert_eq!(
            compiler.retained_product_generation(root, &super::ProductKey::NativeProgram(root)),
            Some(1)
        );
    }

    // AOT front door: NativeProgram still produced, through one explicit demand.
    {
        let tel = ConfiguredTelemetry::new();
        let lowered = capture_native_lowerings(&tel);
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("fixtures/aot_still_lowers_native.fz".to_string()),
            text: source.to_string(),
        });
        let root = compiler.submit_root(super::RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: super::ExecutableNeed::Value,
        });

        compiler
            .compile_root_aot(root, "interp_never_lowers_native_aot")
            .unwrap_or_else(|error| panic!("enum_reduce_operator_ref should AOT-compile: {error}"));

        assert_eq!(
            lowered.get(),
            1,
            "the AOT front door demands NativeProgram exactly once through compile_root_aot",
        );
        assert_eq!(
            compiler.retained_product_generation(root, &super::ProductKey::NativeProgram(root)),
            Some(1)
        );
    }
}

fn capture_native_lowerings(telemetry: &ConfiguredTelemetry) -> Rc<Cell<u64>> {
    let count = Rc::new(Cell::new(0));
    let sink = Rc::clone(&count);
    telemetry.attach_raw_event2::<super::RootId, super::BackendProgram, _>(
        &["fz", "compiler2", "native_program", "reusable_cons"],
        move |_, _, _, _, _| sink.set(sink.get() + 1),
    );
    count
}

#[derive(Debug, Clone)]
struct JobSpanStart {
    job: Job,
    parent_span_id: u64,
}

#[derive(Debug, Clone)]
struct JobSpanStop {
    job: Job,
    parent_span_id: u64,
}

struct JobCapture {
    starts: Rc<RefCell<Vec<JobSpanStart>>>,
    stops: Rc<RefCell<Vec<JobSpanStop>>>,
}

impl JobCapture {
    fn new() -> Self {
        Self {
            starts: Rc::new(RefCell::new(Vec::new())),
            stops: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn install(&self, telemetry: &ConfiguredTelemetry) {
        let starts = Rc::clone(&self.starts);
        let stops = Rc::clone(&self.stops);
        let jobs_by_span = Rc::new(RefCell::new(HashMap::new()));
        let started_jobs = Rc::clone(&jobs_by_span);
        let stopped_jobs = Rc::clone(&jobs_by_span);
        telemetry.attach_raw_span1_0::<Job, _, _, _>(
            &["fz", "compiler2", "job"],
            move |_, span_id, parent_span_id, job| {
                started_jobs.borrow_mut().insert(span_id, job.clone());
                starts.borrow_mut().push(JobSpanStart {
                    job: job.clone(),
                    parent_span_id,
                });
            },
            move |_, span_id, parent_span_id, _| {
                stops.borrow_mut().push(JobSpanStop {
                    job: stopped_jobs
                        .borrow_mut()
                        .remove(&span_id)
                        .expect("a job span stop must match its start"),
                    parent_span_id,
                });
            },
            |_, _, _, _| {},
        );
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

#[test]
fn env_in_function_body_resolves_via_namespace_splice() {
    // A function body that names __ENV__ must compile: just before the body is
    // expanded, __ENV__ is bound in the namespace to the definition env (a map
    // snippet) and the expander splices it in. Without that binding __ENV__ is
    // an unbound variable and the drive cannot resolve.
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("env_body.fz".to_string()),
        text: "fn main(), do: __ENV__\n".to_string(),
    });
    let _root = compiler.submit_root(super::RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: super::ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Resolved),
        "a function body referencing __ENV__ should resolve once __ENV__ is spliced from the namespace"
    );
}

#[test]
fn compiler2_macro_ignoring_caller_runs_with_elided_caller_lane() {
    // A macro whose body never uses __CALLER__ leaves that input Nothing-shaped,
    // so the executable carries no runtime lane for it. The macro caller
    // (run_macro_on_source) must honor that elision from the executable's lane
    // layout rather than pass a fixed [__CALLER__, args] ABI; otherwise the entry
    // is handed one lane too many ("expected 1 runtime lane(s), got 2").
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_caller_elision.fz".to_string()),
        text: "defmacro inc(x) do\n  quote do: unquote(x) + 1\nend\n\nfn main(), do: inc(41)\n".to_string(),
    });
    let root = compiler.submit_root(super::RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: super::ExecutableNeed::Value,
    });
    assert_eq!(
        compiler
            .run_root_interp(root)
            .expect("a macro ignoring __CALLER__ should expand and run"),
        42,
        "inc(41) should evaluate to 42 with the unused __CALLER__ lane elided",
    );
}

fn drive_and_count_function_source_production(name: &str, source: &str) -> (usize, usize) {
    let tel = ConfiguredTelemetry::new();
    let stashed = Rc::new(RefCell::new(HashSet::<super::FunctionId>::new()));
    let stash_sink = Rc::clone(&stashed);
    tel.attach_raw_event3::<super::World, super::FunctionId, super::FunctionSource, _>(
        &["fz", "compiler2", "compiler_service", "define"],
        move |_, _, _, _, function, _| {
            stash_sink.borrow_mut().insert(*function);
        },
    );

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(super::RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: super::ExecutableNeed::Value,
    });
    compiler
        .drive_root_backend_work_starts(root)
        .unwrap_or_else(|error| panic!("{name} should drive to its backend product: {error}"));
    assert!(
        !compiler.retained_backend_program(root).executables.is_empty(),
        "{name} should settle a backend product with executable functions",
    );

    let stashed = stashed.borrow();
    let stash_count = stashed.len();
    let minted = stashed
        .iter()
        .filter(|&&id| compiler.world().has_fact(&super::FactKey::FunctionSource(id)))
        .count();

    (minted, stash_count)
}

#[test]
fn function_source_is_demand_minted_not_stash_eager() {
    for (name, source) in [
        (
            "quicksort_plus_foo.fz",
            include_str!("../../fixtures2/00001_quicksort_plus_foo.fz"),
        ),
        (
            "make_resource.fz",
            include_str!("../../fixtures2/00026_make_resource.fz"),
        ),
        (
            "enum_reduce_operator_ref.fz",
            include_str!("../../fixtures2/00181_enum_reduce_operator_ref.fz"),
        ),
    ] {
        let (minted, stash) = drive_and_count_function_source_production(name, source);
        assert!(minted > 0, "{name} should demand at least one function source");
        assert!(
            minted < stash,
            "{name} should leave unreached function sources unminted: minted={minted}, stash={stash}",
        );
    }
}
