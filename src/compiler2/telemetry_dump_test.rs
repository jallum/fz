use std::path::Path;
use std::time::Duration;

use crate::telemetry::capture::vec_writer;
use crate::telemetry::{Capture, ConfiguredTelemetry, JsonlBackend, Telemetry as _};

use super::dump::{DumpKind, DumpSpec, install_dump_handlers};
use super::{CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, RootSubmission};

/// The user-facing `types`/`activations` dumps are served from the PRODUCT-PATH
/// activation inventory (`emit_product_semantic_dumps`). There is no legacy
/// semantic-closure seal to route around — it was deleted (fz-go4.18.4). This
/// pins that the product dump producer emits the per-activation dump events and
/// that they carry the real root-owned activation facts.
#[test]
fn semantic_dumps_serve_from_the_product_path() {
    let capture = Capture::new();
    let tel = ConfiguredTelemetry::new();
    tel.attach(&[], capture.handler());

    // Wire the real CLI dump sinks so the assertion exercises the full
    // production chain: product drive -> dump events -> file handlers.
    let dir = std::env::temp_dir().join(format!("fz-go4-18-7-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create dump temp dir");
    let types_path = dir.join("types.txt");
    let activations_path = dir.join("activations.txt");

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures2/00001_quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    install_dump_handlers(
        compiler.telemetry(),
        root,
        &[
            DumpSpec {
                kind: DumpKind::Types,
                path: types_path.clone(),
            },
            DumpSpec {
                kind: DumpKind::Activations,
                path: activations_path.clone(),
            },
        ],
    );

    compiler
        .emit_product_semantic_dumps(root)
        .expect("product-path semantic dumps should resolve");

    // The dump events fire — the feature is served.
    assert!(
        capture.contains(&["fz", "compiler2", "dump", "types"]),
        "the types dump event should be emitted from the product path"
    );
    assert!(
        capture.contains(&["fz", "compiler2", "dump", "activations"]),
        "the activations dump event should be emitted from the product path"
    );

    // The activation SET came from the product inventory, so the dump carries
    // the real per-activation facts (here: the root-owned quicksort activations).
    let types_text = std::fs::read_to_string(&types_path).expect("types dump should be written");
    for expected in ["main/0[]", "qsort/1", "partition/4", "append/2"] {
        assert!(
            types_text.contains(expected),
            "product-path types dump should list `{expected}`; got:\n{types_text}"
        );
    }
    assert!(
        std::fs::read_to_string(&activations_path)
            .expect("activations dump should be written")
            .contains("return:"),
        "product-path activations dump should carry per-activation return facts"
    );
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
#[ignore = "manual trace harness for one-off Compiler2 telemetry analysis"]
fn dump_quicksort_compiler2_telemetry_to_jsonl() {
    let path = Path::new("/tmp/fz-compiler2-quicksort.jsonl");
    let tel = ConfiguredTelemetry::new();
    tel.attach(&[], Box::new(JsonlBackend::new_file(path).expect("open log file")));

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: include_str!("../../fixtures2/00001_quicksort_plus_foo.fz").to_string(),
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

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce_runtime_graph.fz".to_string()),
        text: include_str!("../../fixtures2/00010_enum_reduce_main.fz").to_string(),
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

    let mut compiler = Compiler2::new(tel);
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

#[test]
fn jsonl_backend_records_compiler2_drive_timeouts() {
    let (buf, writer) = vec_writer();
    let tel = ConfiguredTelemetry::new();
    tel.attach(&[], Box::new(JsonlBackend::new_writer(writer)));

    let mut compiler = Compiler2::new(tel);
    compiler.set_drive_timeout(Duration::ZERO);
    compiler.submit_code(CodeSubmission {
        name: Some("timeout_main.fz".to_string()),
        text: "fn main(), do: 0\n".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let error = compiler
        .run_root_interp(root)
        .expect_err("zero drive timeout should abort before compiler work runs");
    assert!(
        error.contains("exceeded 0 ms drive limit"),
        "timeout should surface through the compiler entrypoint, got: {error}"
    );

    let log = String::from_utf8(buf.borrow().clone()).expect("jsonl log should stay utf-8");
    assert!(
        log.contains("\"name\":[\"fz\",\"compiler2\",\"drive\",\"timed_out\"]"),
        "compiler2 jsonl log should record drive timeout events:\n{log}"
    );
    assert!(
        log.contains("\"timeout_ms\":0"),
        "drive timeout telemetry should record the configured timeout in milliseconds:\n{log}"
    );
}
