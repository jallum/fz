use super::{CodeSubmission, Compiler2, Job};
use crate::compiler2::FactKey;
use crate::compiler2::work::JobEffects;
use crate::diag::codes;
use crate::telemetry::capture::OwnedEvent;
use crate::telemetry::handler::{Event, EventKind, Handler};
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

type OutputFacts = Vec<(FactKey, u64)>;
type OutputSlot = Rc<RefCell<Option<OutputFacts>>>;
type SpanIdSet = Rc<RefCell<HashSet<u64>>>;

#[test]
fn compiler2_index_code_defines_owned_functions_without_lowering_or_activating_bodies() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    let source = format!(
        "{}\nfn foo(), do: 42\n",
        include_str!("../../fixtures/quicksort/input.fz")
    );

    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: source,
    });

    assert_eq!(
        job_stops(&capture, "IndexCode").len(),
        0,
        "submit_code should not index eagerly"
    );

    compiler.drive().expect("first drive should index quicksort plus foo");

    let indexed_start = job_start(&capture, "IndexCode", code_id.as_u32() as u64);
    let indexed_stop = job_stop(&capture, &indexed_start);
    assert_eq!(
        metadata_str(&indexed_stop, "outcome"),
        "ok",
        "indexing job should finish ok"
    );

    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for quicksort plus foo"
    );
    compiler.drive().expect("second drive should define quicksort plus foo");

    let mut names = capture
        .find(&["fz", "compiler2", "function", "defined"])
        .into_iter()
        .map(|event| {
            (
                metadata_str(&event, "name").to_string(),
                measurement_u64(&event, "arity"),
                metadata_str(&event, "module_name").to_string(),
                metadata_str(&event, "fq_name").to_string(),
                metadata_str(&event, "kind").to_string(),
                measurement_u64(&event, "clauses"),
            )
        })
        .collect::<Vec<_>>();
    names.sort_by(|left, right| left.0.cmp(&right.0).then(left.1.cmp(&right.1)));
    assert_eq!(
        names
            .iter()
            .map(|(name, arity, module, fq_name, kind, clauses)| {
                (
                    name.as_str(),
                    *arity,
                    module.as_str(),
                    fq_name.as_str(),
                    kind.as_str(),
                    *clauses,
                )
            })
            .collect::<Vec<_>>(),
        vec![
            ("append", 2, "<top-level>", "append", "function", 2),
            ("foo", 0, "<top-level>", "foo", "function", 1),
            ("main", 0, "<top-level>", "main", "function", 1),
            ("partition", 4, "<top-level>", "partition", "function", 3),
            ("qsort", 1, "<top-level>", "qsort", "function", 2),
        ],
        "function.defined should publish the expected top-level definitions"
    );

    assert_eq!(
        capture.count(&["fz", "compiler2", "function", "defined"]),
        5,
        "indexing should emit one function.defined event per function"
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "code", "indexed"]),
        0,
        "indexing should not emit a separate code.indexed event"
    );
    assert_eq!(
        job_stops(&capture, "IndexCode").len(),
        1,
        "indexing should close one IndexCode job span"
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "fact", "published"]),
        0,
        "indexing should not emit redundant fact.published telemetry"
    );

    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "indexing should stay above lowering"
    );
    assert_eq!(
        capture.count(&["fz", "planner", "planned"]),
        0,
        "indexing should stay above planning"
    );

    let outputs = outputs.take().expect("IndexCode job effects");
    assert_eq!(
        outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::FunctionDefined(_)))
            .count(),
        0,
        "index_code outputs should stay in discovery and not define functions directly"
    );
    assert_eq!(
        outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleDefined(_)))
            .count(),
        0,
        "top-level quicksort indexing should not define modules directly"
    );
    assert_eq!(
        outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleIndexed(_)))
            .count(),
        0,
        "top-level quicksort indexing should not discover nested modules"
    );
    assert!(
        outputs.contains(&(FactKey::CodeIndexed(code_id), 1)),
        "IndexCode outputs should include the final code-indexed fact"
    );
}

#[test]
fn compiler2_index_code_recurses_through_nested_modules() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/nested_modules.fz".to_string()),
        text: r#"
defmodule X do
  defmodule Y do
    defmodule Z do
      fn func(), do: 20
    end
  end
end
"#
        .to_string(),
    });

    compiler.drive().expect("first drive should index nested module scopes");
    let indexed_outputs = outputs.take().expect("IndexCode job effects");
    let module_ids = module_indexed_ids(&indexed_outputs);
    assert_eq!(module_ids.len(), 3, "nested indexing should discover X, X.Y, and X.Y.Z");

    let indexed_start = job_start(&capture, "IndexCode", code_id.as_u32() as u64);
    let indexed_stop = job_stop(&capture, &indexed_start);
    assert_eq!(
        metadata_str(&indexed_stop, "outcome"),
        "ok",
        "indexing job should finish ok"
    );

    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for nested modules"
    );
    compiler
        .drive()
        .expect("second drive should scope the root module declarations");

    assert_eq!(
        capture.count(&["fz", "compiler2", "module", "defined"]),
        0,
        "root definition should not eagerly define nested modules"
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "function", "defined"]),
        0,
        "root definition should not eagerly define nested functions"
    );

    assert!(
        compiler.demand(Job::DefineModule(*module_ids.last().expect("deepest module id"))),
        "explicit demand should enqueue the nested module definition"
    );
    compiler
        .drive()
        .expect("third drive should define the demanded nested module and its parents");

    let mut defined_modules = capture
        .find(&["fz", "compiler2", "module", "defined"])
        .into_iter()
        .map(|event| metadata_str(&event, "module_name").to_string())
        .collect::<Vec<_>>();
    defined_modules.sort();
    assert_eq!(
        defined_modules,
        vec!["X", "X.Y", "X.Y.Z"],
        "module.defined should emit one event per nested module"
    );

    let function_defined = capture
        .find(&["fz", "compiler2", "function", "defined"])
        .into_iter()
        .next()
        .expect("nested function.defined event");
    assert_eq!(
        metadata_str(&function_defined, "module_name"),
        "X.Y.Z",
        "nested function should be attributed to its fully-qualified module"
    );
    assert_eq!(
        metadata_str(&function_defined, "fq_name"),
        "X.Y.Z.func",
        "nested function should publish its fully-qualified function name"
    );
    assert_eq!(
        measurement_u64(&function_defined, "arity"),
        0,
        "nested function arity should be preserved"
    );

    assert_eq!(
        indexed_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleIndexed(_)))
            .count(),
        3,
        "nested indexing should surface one module-indexed fact per nested module"
    );
    assert_eq!(
        indexed_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::FunctionDefined(_)))
            .count(),
        0,
        "nested indexing should not define functions directly"
    );
    assert_eq!(
        indexed_outputs
            .iter()
            .filter(|(fact, _)| matches!(fact, FactKey::ModuleDefined(_)))
            .count(),
        0,
        "nested indexing should not define modules directly"
    );
    assert!(
        indexed_outputs.contains(&(FactKey::CodeIndexed(code_id), 1)),
        "nested indexing should include the final code-indexed fact"
    );
}

#[test]
fn compiler2_import_only_waits_for_defined_module_surface() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_only.fz".to_string()),
        text: r#"
defmodule User do
  import Math, only: [add: 1, add: 2]
  fn run(), do: add(20, 22)
end

defmodule Math do
  fn add(a), do: a
  fn add(a, b), do: a + b
end
"#
        .to_string(),
    });

    compiler.drive().expect("first drive should index import-only scope");
    let module_ids = module_indexed_ids(&outputs.take().expect("IndexCode job effects"));
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-only scope"
    );
    compiler.drive().expect("second drive should scope import-only modules");
    assert_eq!(
        capture.count(&["fz", "compiler2", "function", "defined"]),
        0,
        "root definition should not eagerly define import-only modules"
    );
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    compiler
        .drive()
        .expect("third drive should define Math before retrying User");
    let mut names = capture
        .find(&["fz", "compiler2", "function", "defined"])
        .into_iter()
        .map(|event| {
            (
                metadata_str(&event, "fq_name").to_string(),
                measurement_u64(&event, "arity"),
            )
        })
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(
        names,
        vec![
            ("Math.add".to_string(), 1),
            ("Math.add".to_string(), 2),
            ("User.run".to_string(), 0),
        ],
        "import-only indexing should preserve the imported overloads alongside the consumer"
    );
}

#[test]
fn compiler2_import_only_reports_unknown_import_after_surface_is_defined() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_only_unknown.fz".to_string()),
        text: r#"
defmodule User do
  import Math, only: [missing: 1]
  fn run(), do: missing(20)
end

defmodule Math do
  fn add(a), do: a
end
"#
        .to_string(),
    });

    compiler
        .drive()
        .expect("first drive should index import-only unknown scope");
    let module_ids = module_indexed_ids(&outputs.take().expect("IndexCode job effects"));
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-only unknown scope"
    );
    compiler
        .drive()
        .expect("second drive should scope import-only unknown modules");
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    let err = compiler
        .drive()
        .expect_err("third drive should fail once Math's defined surface lacks missing/1");
    assert_eq!(
        err.job,
        Job::DefineModule(module_ids[0]),
        "fatal job should be the retried consumer module"
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("unknown import diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::RESOLVE_UNKNOWN_IMPORT.0,
        "only: should validate against the provider surface"
    );
    assert!(
        metadata_str(&diagnostic, "message").contains("missing/1"),
        "diagnostic should name the missing import"
    );
}

#[test]
fn compiler2_import_all_waits_for_defined_module_surface() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_all.fz".to_string()),
        text: r#"
defmodule User do
  import Math
  fn run(), do: add(20, 22)
end

defmodule Math do
  fn add(a), do: a
  fn add(a, b), do: a + b
end
"#
        .to_string(),
    });

    compiler.drive().expect("first drive should index import-all scope");
    let module_ids = module_indexed_ids(&outputs.take().expect("IndexCode job effects"));
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-all scope"
    );
    compiler.drive().expect("second drive should scope import-all modules");
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    compiler
        .drive()
        .expect("third drive should define Math before retrying User");
    let mut names = capture
        .find(&["fz", "compiler2", "function", "defined"])
        .into_iter()
        .map(|event| {
            (
                metadata_str(&event, "fq_name").to_string(),
                measurement_u64(&event, "arity"),
            )
        })
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(
        names,
        vec![
            ("Math.add".to_string(), 1),
            ("Math.add".to_string(), 2),
            ("User.run".to_string(), 0),
        ],
        "import-all indexing should keep the imported module surface and the consumer function intact"
    );
}

#[test]
fn compiler2_import_except_waits_for_defined_module_surface() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/import_except.fz".to_string()),
        text: r#"
defmodule User do
  import Math, except: [add: 1]
  fn run(), do: add(20, 22)
end

defmodule Math do
  fn add(a), do: a
  fn add(a, b), do: a + b
  fn sub(a, b), do: a - b
end
"#
        .to_string(),
    });

    compiler.drive().expect("first drive should index import-except scope");
    let module_ids = module_indexed_ids(&outputs.take().expect("IndexCode job effects"));
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-except scope"
    );
    compiler
        .drive()
        .expect("second drive should scope import-except modules");
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    compiler
        .drive()
        .expect("third drive should define Math before retrying User");
    let mut names = capture
        .find(&["fz", "compiler2", "function", "defined"])
        .into_iter()
        .map(|event| {
            (
                metadata_str(&event, "fq_name").to_string(),
                measurement_u64(&event, "arity"),
            )
        })
        .collect::<Vec<_>>();
    names.sort();
    assert_eq!(
        names,
        vec![
            ("Math.add".to_string(), 1),
            ("Math.add".to_string(), 2),
            ("Math.sub".to_string(), 2),
            ("User.run".to_string(), 0),
        ],
        "import-except indexing should still define the provider surface and the consumer"
    );
}

struct OutputCapture {
    outputs: OutputSlot,
    index_spans: SpanIdSet,
}

impl OutputCapture {
    fn new() -> Self {
        Self {
            outputs: Rc::new(RefCell::new(None)),
            index_spans: Rc::new(RefCell::new(HashSet::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(OutputCaptureHandler {
            outputs: self.outputs.clone(),
            index_spans: self.index_spans.clone(),
        })
    }

    fn take(&self) -> Option<OutputFacts> {
        self.outputs.borrow_mut().take()
    }
}

struct OutputCaptureHandler {
    outputs: OutputSlot,
    index_spans: SpanIdSet,
}

impl Handler for OutputCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "job"] {
            return;
        }
        match event.kind {
            EventKind::SpanStart => {
                if matches!(event.metadata.get("kind"), Some(Value::Str(kind)) if kind.as_ref() == "IndexCode") {
                    self.index_spans.borrow_mut().insert(event.span_id);
                }
            }
            EventKind::SpanStop => {
                if !self.index_spans.borrow_mut().remove(&event.span_id) {
                    return;
                }
                let effects = event
                    .metadata
                    .get("effects")
                    .and_then(|value| value.downcast_ref::<JobEffects>())
                    .expect("IndexCode job stop should expose job effects");
                self.outputs.replace(Some(effects.outputs.clone()));
            }
            EventKind::Event | EventKind::SpanException => {}
        }
    }
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

fn measurement_u64(event: &OwnedEvent, key: &str) -> u64 {
    match event.measurements.get(key) {
        Some(Value::U64(value)) => *value,
        other => panic!("measurement key `{key}` missing or not u64: {other:?}"),
    }
}

fn metadata_str<'a>(event: &'a OwnedEvent, key: &str) -> &'a str {
    match event.metadata.get(key) {
        Some(Value::Str(value)) => value.as_ref(),
        other => panic!("metadata key `{key}` missing or not str: {other:?}"),
    }
}

fn module_indexed_ids(outputs: &OutputFacts) -> Vec<crate::compiler2::ModuleId> {
    outputs
        .iter()
        .filter_map(|(fact, _)| match fact {
            FactKey::ModuleIndexed(module_id) => Some(*module_id),
            _ => None,
        })
        .collect()
}
