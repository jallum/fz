use std::cell::RefCell;
use std::collections::HashSet;
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
    output.program(&world, root);
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
    assert!(
        log.contains("\"formula_id\":\"SeedRoot(RootId(0))\"")
            && log.contains("\"causes\":[{\"kind\":\"demand\",\"reason\":\"ignition\"}]")
            && log.contains("\"changed_facts\":[]"),
        "compiler2 jsonl log should expose stable formula identity and exact evaluation causality:\n{log}"
    );
}

#[test]
fn jsonl_backend_exposes_stable_product_identity_generations_and_dependencies() {
    let (buf, writer) = vec_writer();
    let tel = ConfiguredTelemetry::new();
    JsonlBackend::new_writer(writer).install(&tel);

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("product_causality.fz".to_string()),
        text: "fn main(), do: 1".to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .run_root_interp(root)
        .expect("the product trace fixture should run");
    drop(compiler);

    let log = String::from_utf8(buf.borrow().clone()).expect("jsonl log should stay utf-8");
    assert!(
        log.contains("\"action\":\"evaluated\"")
            && log.contains("\"action\":\"settled\"")
            && log.contains("\"product_id\":\"RootBackendProduct(0)\"")
            && log.contains("\"previous_generation\":null")
            && log.contains("\"generation\":1")
            && log.contains("\"changed\":true")
            && log.contains("\"dependencies\":{\"products\":[")
            && log.contains("\"recursive_group_candidates\":")
            && log.contains("\"dependency_reach_visits\":"),
        "compiler2 jsonl log should expose product identity and causal state from the product memo:\n{log}"
    );
}

#[test]
fn compiler2_causal_work_multiset_is_stable_across_repeated_runs() {
    fn causal_trace() -> Vec<String> {
        let (buf, writer) = vec_writer();
        let tel = ConfiguredTelemetry::new();
        JsonlBackend::new_writer(writer).install(&tel);
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("causal_trace.fz".to_string()),
            text: "fn main(), do: 1".to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        compiler
            .run_root_interp(root)
            .expect("the causal trace fixture should run");
        drop(compiler);

        let log = String::from_utf8(buf.borrow().clone()).expect("jsonl log should stay utf-8");
        let mut trace = log
            .lines()
            .filter_map(|line| {
                let event: serde_json::Value = serde_json::from_str(line)
                    .unwrap_or_else(|error| panic!("telemetry line should be JSON: {error}: {line}"));
                ["causality", "product_causality", "product_group"]
                    .into_iter()
                    .find_map(|field| event.get(field).map(|value| format!("{field}:{value}")))
            })
            .collect::<Vec<_>>();
        trace.sort();
        trace
    }

    assert_eq!(causal_trace(), causal_trace());
}

#[test]
fn target_fixture_public_logs_are_self_sufficient_causal_work_traces() {
    for (name, source) in [
        (
            "enum_take_drop_split",
            include_str!("../../fixtures2/behavior/enum_take_drop_split.fz"),
        ),
        (
            "fz_f98_range_map_converges",
            include_str!("../../fixtures2/behavior/fz_f98_range_map_converges.fz"),
        ),
        (
            "enum_predicate_search",
            include_str!("../../fixtures2/behavior/enum_predicate_search.fz"),
        ),
    ] {
        let (buf, writer) = vec_writer();
        let tel = ConfiguredTelemetry::new();
        JsonlBackend::new_public_writer(writer).install(&tel);
        let dbg = crate::exec::runtime::DbgCapture::new();
        let mut compiler = Compiler2::new(tel);
        compiler.set_output(dbg.sink());
        compiler.submit_code(CodeSubmission {
            name: Some(format!("{name}.fz")),
            text: source.to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        compiler
            .run_root_interp(root)
            .unwrap_or_else(|error| panic!("{name} should compile and run while tracing causal work: {error}"));
        drop(compiler);

        let log = String::from_utf8(buf.borrow().clone()).expect("public log should stay utf-8");
        let events = log
            .lines()
            .map(|line| {
                serde_json::from_str::<serde_json::Value>(line)
                    .unwrap_or_else(|error| panic!("{name} public telemetry must be JSON: {error}: {line}"))
            })
            .collect::<Vec<_>>();
        let causal = events
            .iter()
            .filter_map(|event| event.get("causality"))
            .collect::<Vec<_>>();
        assert!(!causal.is_empty(), "{name} should expose job causality");
        assert!(
            causal.iter().all(|record| {
                record["formula_id"].as_str().is_some_and(|id| !id.contains("Ty("))
                    && record["causes"].as_array().is_some_and(|causes| !causes.is_empty())
                    && record["changed_facts"].is_array()
                    && record["wakes"].is_array()
            }),
            "{name} job records should carry stable identity, exact causes, changes, and wakes"
        );
        let formula_ids = causal
            .iter()
            .filter_map(|record| record["formula_id"].as_str())
            .collect::<HashSet<_>>();
        assert!(
            formula_ids.len() > 1,
            "{name} should expose distinct formula identities"
        );

        let products = events
            .iter()
            .filter_map(|event| event.get("product_causality"))
            .collect::<Vec<_>>();
        assert!(!products.is_empty(), "{name} should expose product causality");
        assert!(
            products.iter().all(|record| {
                record["product_id"].as_str().is_some_and(|id| !id.contains("Ty(")) && record["action"].is_string()
            }),
            "{name} product records should carry stable identity and action"
        );
        assert!(
            products
                .iter()
                .filter(|record| record["action"] == "evaluated")
                .all(|record| record["dependencies"].is_object()),
            "{name} product evaluations should carry exact dependency states"
        );
        assert!(
            products
                .iter()
                .filter(|record| record["action"] == "settled")
                .all(|record| record["generation"].is_u64() && record["changed"].is_boolean()),
            "{name} product settlements should carry generation movement"
        );
    }
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
