use std::cell::RefCell;
use std::path::Path;
use std::rc::Rc;
use std::time::Duration;

use crate::telemetry::capture::vec_writer;
use crate::telemetry::{ConfiguredTelemetry, JsonlBackend};

use super::dump::{DumpKind, DumpSpec, FileRequestedOutput, NullRequestedOutput, RequestedOutputSink};
use super::{CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, RootSubmission};

#[test]
fn null_requested_output_is_inert() {
    let mut output = NullRequestedOutput;
    let world = super::World::new();
    let root = super::RootId::for_test(1);

    assert!(!output.wants_clif());
    output.semantic(&world, root, &[]);
    let backend = super::BackendProgram::empty_for_test();
    output.program(&world, root, &backend, None);
}

#[test]
fn clif_output_observes_populated_functions() {
    struct ClifCapture(Rc<RefCell<Vec<String>>>);

    impl RequestedOutputSink for ClifCapture {
        fn wants_clif(&self) -> bool {
            true
        }

        fn clif(
            &mut self,
            _: &crate::fz_ir::Module,
            _: crate::fz_ir::FnId,
            function: &cranelift_codegen::ir::Function,
        ) {
            self.0.borrow_mut().push(function.display().to_string());
        }
    }

    let observed = Rc::new(RefCell::new(Vec::new()));
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.set_requested_output(Box::new(ClifCapture(Rc::clone(&observed))));
    compiler.submit_code(CodeSubmission {
        name: Some("clif_output.fz".to_string()),
        text: "fn main(), do: 0\n".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    compiler.compile_root_jit(root).expect("JIT compile");

    let observed = observed.borrow();
    assert!(!observed.is_empty());
    assert!(observed.iter().all(|function| function.contains("block0")));
}

/// The user-facing `types`/`activations` dumps are served from the product-path
/// activation inventory (`emit_product_semantic_dumps`). The product dump
/// producer emits per-activation events carrying the root-owned facts.
#[test]
fn semantic_dumps_serve_from_the_product_path() {
    let tel = ConfiguredTelemetry::new();

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

    compiler.set_requested_output(Box::new(FileRequestedOutput::new(
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
    )));

    compiler
        .emit_product_semantic_dumps(root)
        .expect("product-path semantic dumps should resolve");

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
    JsonlBackend::new_file(path).expect("open log file").install(&tel);

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
    JsonlBackend::new_file(path).expect("open log file").install(&tel);

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
    JsonlBackend::new_writer(writer).install(&tel);

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
        log.contains("\"completion\":{\"opaque_type\"") && log.contains("FunctionDefined"),
        "compiler2 jsonl log should show the blocking fact in the applied step:\n{log}"
    );
    assert!(
        log.contains("\"status\":\"unresolved\"") && log.contains("\"wait_count\":"),
        "compiler2 jsonl log should surface the unresolved drive outcome and wait count:\n{log}"
    );
    assert!(
        log.contains("\"world\":{\"opaque_type\":\"fz::compiler2::world::World\",\"codes\":")
            && log.contains("\"activation_frontier\":"),
        "compiler2 jsonl log should project world state from the borrowed authority:\n{log}"
    );
}

#[test]
fn jsonl_backend_records_compiler2_drive_timeouts() {
    let (buf, writer) = vec_writer();
    let tel = ConfiguredTelemetry::new();
    JsonlBackend::new_writer(writer).install(&tel);

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
