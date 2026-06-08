use std::path::Path;

use crate::telemetry::capture::vec_writer;
use crate::telemetry::{ConfiguredTelemetry, JsonlBackend, Telemetry as _};

use super::{CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, RootSubmission};

#[test]
#[ignore = "manual trace harness for one-off Compiler2 telemetry analysis"]
fn dump_quicksort_compiler2_telemetry_to_jsonl() {
    let path = Path::new("/tmp/fz-compiler2-quicksort.jsonl");
    let tel = ConfiguredTelemetry::new();
    tel.attach(&[], Box::new(JsonlBackend::new_file(path).expect("open log file")));

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    match compiler.drive() {
        DriveOutcome::Resolved => {}
        other => panic!("expected resolved quicksort compilation, got {other:?}"),
    }
}

#[test]
#[ignore = "manual trace harness for one-off Compiler2 telemetry analysis"]
fn dump_enum_reduce_compiler2_telemetry_to_jsonl() {
    let path = Path::new("/tmp/fz-compiler2-enum-reduce.jsonl");
    let tel = ConfiguredTelemetry::new();
    tel.attach(&[], Box::new(JsonlBackend::new_file(path).expect("open log file")));

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_runtime_graph.fz".to_string()),
        text: r#"
fn main(), do: Enum.reduce([1, 2, 3, 4, 5], 0, fn (x, acc) -> x + acc end)
"#
        .to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    match compiler.drive() {
        DriveOutcome::Resolved => {}
        other => panic!("expected resolved Enum.reduce compilation, got {other:?}"),
    }
}

#[test]
fn jsonl_backend_shows_precipitating_compiler2_actions() {
    let (buf, writer) = vec_writer();
    let tel = ConfiguredTelemetry::new();
    tel.attach(&[], Box::new(JsonlBackend::new_writer(writer)));

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    match compiler.drive() {
        DriveOutcome::Unresolved { .. } => {}
        other => panic!("root-before-code should finish unresolved for the log test: {other:?}"),
    }

    let log = String::from_utf8(buf.borrow().clone()).expect("jsonl log should stay utf-8");
    assert!(
        log.contains("\"name\":[\"fz\",\"compiler2\",\"work_graph\",\"applied\"]"),
        "compiler2 jsonl log should include the applied work-graph step:\n{log}"
    );
    assert!(
        log.contains("\"job\":{\"opaque_type\"") && log.contains("SeedRoot"),
        "compiler2 jsonl log should name the job that triggered the unresolved drive:\n{log}"
    );
    assert!(
        log.contains("\"step\":{\"opaque_type\"") && log.contains("FunctionDefined"),
        "compiler2 jsonl log should show the blocking fact in the applied step:\n{log}"
    );
    assert!(
        log.contains("\"waits\":{\"opaque_type\""),
        "compiler2 jsonl log should surface the unresolved wait frontier on the drive span:\n{log}"
    );
}

#[test]
fn dump_harness_uses_the_same_jsonl_backend_as_cli_logging() {
    let (buf, writer) = vec_writer();
    let tel = ConfiguredTelemetry::new();
    tel.attach(&[], Box::new(JsonlBackend::new_writer(writer)));

    tel.event(&["fz", "compiler2", "ping"], crate::metadata! {});

    let log = String::from_utf8(buf.borrow().clone()).expect("jsonl log should stay utf-8");
    assert!(
        log.contains("\"name\":[\"fz\",\"compiler2\",\"ping\"]"),
        "the manual dump harness should rely on the stock jsonl backend format:\n{log}"
    );
}
