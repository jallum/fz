use super::{CodeSubmission, Compiler2, DriveOutcome, ExactPattern, ExecutableNeed, Job, RootSubmission};
use crate::compiler2::drive::JobEffects;
use crate::compiler2::{ActivationKey, ExecutableKey, FactKey, FunctionId};
use crate::diag::codes;
use crate::dispatch_matrix::pattern::{PatternGuardDispatch, PatternGuardExpr};
use crate::telemetry::capture::OwnedEvent;
use crate::telemetry::handler::{Event, EventKind, Handler};
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

type OutputFacts = Vec<(FactKey, u64)>;
type JobOutputMap = Rc<RefCell<HashMap<(String, u64), Vec<OutputFacts>>>>;
type GuardDispatchMap = Rc<RefCell<HashMap<(String, u64), Vec<PatternGuardDispatch>>>>;
type SpanJobs = Rc<RefCell<HashMap<u64, (String, u64)>>>;

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

    assert_resolved(compiler.drive(), "first drive should index quicksort plus foo");

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
    assert_resolved(compiler.drive(), "second drive should define quicksort plus foo");

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
        job_stops(&capture, "LowerFunction").len(),
        0,
        "indexing should not lower any function bodies"
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

    let outputs = outputs
        .take("IndexCode", code_id.as_u32() as u64)
        .expect("IndexCode job effects");
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
fn compiler2_submit_root_pulls_scope_and_seeds_entry_semantics_without_warming_foo() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    let _code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
        text: format!(
            "{}\nfn foo(), do: 42\n",
            include_str!("../../fixtures/quicksort/input.fz")
        ),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "root submission should pull the source surface through to the entry seed",
    );

    let root_submitted = capture
        .last(&["fz", "compiler2", "root", "submitted"])
        .expect("root submitted event");
    assert_eq!(
        measurement_u64(&root_submitted, "root_id"),
        root_id.as_u32() as u64,
        "root submission should report the returned root id"
    );
    assert_eq!(
        metadata_str(&root_submitted, "module_name"),
        "<top-level>",
        "root submission should mark top-level entry functions clearly"
    );
    assert_eq!(
        metadata_str(&root_submitted, "name"),
        "main",
        "root submission should report the entry function name"
    );
    assert_eq!(
        metadata_str(&root_submitted, "need"),
        "value",
        "root submission should report the requested executable need"
    );

    let main_id = function_id(&capture, "main", 0);
    let foo_id = function_id(&capture, "foo", 0);

    let lower_outputs = outputs
        .take("LowerFunction", main_id.as_u32() as u64)
        .expect("LowerFunction job effects for main/0");
    assert!(
        lower_outputs.contains(&(FactKey::LoweredBody(main_id), 1)),
        "submitting a root should lower the entry function body"
    );
    assert!(
        !lower_outputs
            .iter()
            .any(|(fact, _)| matches!(fact, FactKey::LoweredBody(function) if *function == foo_id)),
        "lowering the entry function should keep uncalled foo/0 cold"
    );

    let seed_outputs = outputs
        .take("SeedRoot", root_id.as_u32() as u64)
        .expect("SeedRoot job effects");
    assert!(
        seed_outputs.contains(&(FactKey::RootEntry(root_id), 1)),
        "SeedRoot should publish the root entry fact"
    );
    assert!(
        seed_outputs.contains(&(
            FactKey::Activation(ActivationKey {
                root: root_id,
                function: main_id,
            }),
            1,
        )),
        "SeedRoot should activate the entry function"
    );
    assert!(
        seed_outputs.contains(&(
            FactKey::Executable(ExecutableKey {
                activation: ActivationKey {
                    root: root_id,
                    function: main_id,
                },
                need: ExecutableNeed::Value,
            }),
            1,
        )),
        "SeedRoot should publish the entry executable request"
    );
    assert!(
        !seed_outputs.iter().any(|(fact, _)| {
            matches!(
                fact,
                FactKey::Activation(ActivationKey {
                    function,
                    ..
                }) if *function == foo_id
            ) || matches!(
                fact,
                FactKey::Executable(ExecutableKey {
                    activation: ActivationKey {
                        function,
                        ..
                    },
                    ..
                }) if *function == foo_id
            )
        }),
        "submitting a root should keep uncalled foo/0 semantically cold"
    );

    let closure_outputs = outputs
        .take("CheckSemanticClosure", root_id.as_u32() as u64)
        .expect("CheckSemanticClosure job effects");
    assert!(
        closure_outputs.contains(&(FactKey::SemanticClosed(root_id), 1)),
        "semantic closure should publish once the seeded entry facts exist"
    );

    assert_eq!(
        job_stops(&capture, "ScopeCode").len(),
        1,
        "root submission should pull one top-level scope job for the single code input"
    );
    assert_eq!(
        job_stops(&capture, "SeedRoot").len(),
        2,
        "root submission should publish the root fact first, then rerun once the entry definition exists"
    );
    assert_eq!(
        job_stops(&capture, "CheckSemanticClosure").len(),
        1,
        "root submission should run the initial closure check once"
    );
    assert_eq!(
        job_stops(&capture, "LowerFunction").len(),
        1,
        "root submission should lower only the entry body"
    );
    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "root seeding should not invoke lowering yet"
    );
    assert_eq!(
        capture.count(&["fz", "planner", "planned"]),
        0,
        "root seeding should not invoke the production planner"
    );
}

#[test]
fn compiler2_submit_root_before_code_reports_unresolved_until_entry_is_defined() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    let submitted = capture
        .last(&["fz", "compiler2", "root", "submitted"])
        .expect("root submitted event");
    let function_id = match submitted.measurements.get("function_id") {
        Some(Value::U64(id)) => FunctionId::from_u32(*id as u32),
        other => panic!("root submission missing function_id measurement: {other:?}"),
    };

    let outcome = compiler.drive();
    match outcome {
        DriveOutcome::Unresolved { waits } => {
            assert!(
                waits.iter().any(|wait| {
                    wait.pattern == ExactPattern(FactKey::FunctionDefined(function_id))
                        && wait.jobs.contains(&Job::SeedRoot(root_id))
                }),
                "unresolved drive should report SeedRoot waiting on the entry definition"
            );
        }
        other => panic!("root-before-code should finish unresolved: {other:?}"),
    }

    let drive_stop = capture
        .find(&["fz", "compiler2", "drive"])
        .into_iter()
        .find(|event| event.kind == EventKind::SpanStop)
        .expect("drive stop event");
    assert_eq!(
        metadata_str(&drive_stop, "outcome"),
        "unresolved",
        "drive should close as unresolved while the root is waiting on code"
    );

    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/late_main.fz".to_string()),
        text: "fn main(), do: 42\n".to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "adding the entry definition should resolve the waiting root",
    );
}

#[test]
fn compiler2_submit_code_after_root_auto_scopes_new_definitions_without_reseeding_semantics() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/entry_only.fz".to_string()),
        text: "fn main(), do: 42\n".to_string(),
    });
    let _root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "first drive should seed the initial root");
    assert_eq!(
        job_stops(&capture, "SeedRoot").len(),
        2,
        "entry seeding should settle before later code arrives"
    );

    let late_code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/late_foo.fz".to_string()),
        text: "fn foo(), do: 42\n".to_string(),
    });
    assert_resolved(
        compiler.drive(),
        "second drive should scope late code automatically while a root is active",
    );

    let scope_outputs = outputs
        .take("ScopeCode", late_code_id.as_u32() as u64)
        .expect("late code ScopeCode job effects");
    let foo_id = function_id(&capture, "foo", 0);
    assert!(
        scope_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::FunctionDefined(foo_id)),
        "late code should define foo/0 without an explicit ScopeCode demand"
    );
    assert_eq!(
        job_stops(&capture, "SeedRoot").len(),
        2,
        "late unrelated code should not reseed the existing root"
    );
    assert_eq!(
        job_stops(&capture, "CheckSemanticClosure").len(),
        1,
        "late unrelated code should not reopen semantic closure for the existing root"
    );
    assert_eq!(
        job_stops(&capture, "LowerFunction").len(),
        1,
        "late unrelated code should not lower foo/0 just because a root already exists"
    );
}

#[test]
fn compiler2_lower_function_mints_lambda_defs_without_eagerly_lowering_them() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/enum_reduce.fz".to_string()),
        text: include_str!("../type_infer/fixtures/enum_reduce.fz").to_string(),
    });
    let _root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "rooting enum_reduce should lower only the reachable entry function",
    );

    let main_id = function_id(&capture, "main", 0);
    let lower_outputs = outputs
        .take("LowerFunction", main_id.as_u32() as u64)
        .expect("LowerFunction job effects for enum_reduce main/0");
    let generated = lower_outputs
        .iter()
        .filter_map(|(fact, _)| match fact {
            FactKey::FunctionDefined(function) if *function != main_id => Some(*function),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(
        lower_outputs.contains(&(FactKey::LoweredBody(main_id), 1)),
        "lowering enum_reduce main/0 should publish the lowered body fact"
    );
    assert_eq!(
        generated.len(),
        1,
        "lowering enum_reduce main/0 should mint one generated lambda definition"
    );
    assert!(
        !lower_outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::LoweredBody(generated[0])),
        "lowering main/0 should not eagerly lower the generated reducer lambda"
    );
    assert_eq!(
        job_stops(&capture, "LowerFunction").len(),
        1,
        "lowering enum_reduce should stop at main/0 until something demands the lambda body"
    );
    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "Compiler2 lowering should not invoke the old frontend lowerer"
    );
    assert_eq!(
        capture.count(&["fz", "planner", "planned"]),
        0,
        "Compiler2 lowering should stay above the old planner"
    );
}

#[test]
fn compiler2_guard_dispatch_reifies_single_clause_and_transitive_helpers() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let guard_defs = GuardDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "guard_dispatch", "defined"], guard_defs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_helpers.fz".to_string()),
        text: r#"
fn positive(n), do: n > 0
fn wanted(n), do: positive(n)
"#
        .to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index helper functions");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should scope helper definitions"
    );
    assert_resolved(compiler.drive(), "second drive should define helper functions");

    let positive_id = function_id(&capture, "positive", 1);
    let wanted_id = function_id(&capture, "wanted", 1);

    assert!(
        compiler.demand(Job::ReifyGuardDispatch(positive_id)),
        "dispatch-pure positive/1 should be demandable"
    );
    assert_resolved(compiler.drive(), "positive/1 should reify into a guard dispatch");
    let positive_outputs = outputs
        .take("ReifyGuardDispatch", positive_id.as_u32() as u64)
        .expect("ReifyGuardDispatch job effects for positive/1");
    assert!(
        positive_outputs.contains(&(FactKey::GuardDispatch(positive_id), 1)),
        "positive/1 should publish its guard dispatch fact"
    );
    let positive_dispatch = guard_dispatch(&guard_defs, "positive", 1);
    assert!(
        !guard_dispatch_has_nested_dispatch(&positive_dispatch),
        "single-clause positive/1 should reify directly without nested helper dispatch"
    );

    assert!(
        compiler.demand(Job::ReifyGuardDispatch(wanted_id)),
        "dispatch-pure wanted/1 should be demandable"
    );
    assert_resolved(
        compiler.drive(),
        "wanted/1 should reify through its transitive helper call",
    );
    let wanted_outputs = outputs
        .take("ReifyGuardDispatch", wanted_id.as_u32() as u64)
        .expect("ReifyGuardDispatch job effects for wanted/1");
    assert!(
        wanted_outputs.contains(&(FactKey::GuardDispatch(wanted_id), 1)),
        "wanted/1 should publish its guard dispatch fact"
    );
    let wanted_dispatch = guard_dispatch(&guard_defs, "wanted", 1);
    assert!(
        guard_dispatch_has_nested_dispatch(&wanted_dispatch),
        "transitive helper calls should reify as nested guard dispatch"
    );
}

#[test]
fn compiler2_guard_dispatch_threads_call_arguments_and_destructuring() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let outputs = OutputCapture::new();
    tel.attach(&["fz", "compiler2", "job"], outputs.handler());
    let guard_defs = GuardDispatchCapture::new();
    tel.attach(&["fz", "compiler2", "guard_dispatch", "defined"], guard_defs.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_destructure.fz".to_string()),
        text: r#"
fn positive(n), do: n > 0
fn within(limit, n), do: positive(n + limit)
fn wanted({:ok, {n, _}}), do: within(1, n)
fn wanted(_), do: false
"#
        .to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index destructuring helpers");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should scope destructuring helpers"
    );
    assert_resolved(compiler.drive(), "second drive should define destructuring helpers");

    let wanted_id = function_id(&capture, "wanted", 1);
    assert!(
        compiler.demand(Job::ReifyGuardDispatch(wanted_id)),
        "multi-clause wanted/1 should be demandable"
    );
    assert_resolved(
        compiler.drive(),
        "wanted/1 should reify destructuring heads and threaded helper args",
    );

    let wanted_outputs = outputs
        .take("ReifyGuardDispatch", wanted_id.as_u32() as u64)
        .expect("ReifyGuardDispatch job effects for destructuring wanted/1");
    assert!(
        wanted_outputs.contains(&(FactKey::GuardDispatch(wanted_id), 1)),
        "multi-clause wanted/1 should publish its guard dispatch fact"
    );
    let wanted_dispatch = guard_dispatch(&guard_defs, "wanted", 1);
    assert_eq!(
        wanted_dispatch.bodies.len(),
        2,
        "multi-clause helper reification should preserve one body per clause"
    );
    assert!(
        wanted_dispatch
            .plan
            .outcomes
            .iter()
            .flat_map(|outcome| outcome.bindings.iter())
            .any(|binding| binding.name == "n"),
        "destructuring helper reification should preserve inner bound names"
    );
    assert!(
        guard_dispatch_has_binary_nested_input(&wanted_dispatch),
        "nested helper calls should thread computed call arguments into the nested dispatch"
    );
}

#[test]
fn compiler2_guard_dispatch_rejects_cycles() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_cycle.fz".to_string()),
        text: r#"
fn a(n), do: b(n)
fn b(n), do: a(n)
"#
        .to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index cyclic helpers");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should scope cyclic helpers"
    );
    assert_resolved(compiler.drive(), "second drive should define cyclic helpers");

    let a_id = function_id(&capture, "a", 1);
    assert!(
        compiler.demand(Job::ReifyGuardDispatch(a_id)),
        "cyclic helper should still be demandable"
    );
    let outcome = compiler.drive();
    let job = match outcome {
        DriveOutcome::Fatal { job } => job,
        other => panic!("cyclic helper reification should fail fatally: {other:?}"),
    };
    assert_eq!(
        job,
        Job::ReifyGuardDispatch(a_id),
        "fatal job should be the demanded helper reification"
    );

    let diagnostic = capture.last(&["fz", "diag", "error"]).expect("cycle diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::LOWER_UNSUPPORTED.0,
        "helper cycles should surface as unsupported guard reification"
    );
    assert!(
        metadata_str(&diagnostic, "message").contains("cycle detected"),
        "cycle diagnostic should say why helper reification failed"
    );
}

#[test]
fn compiler2_guard_dispatch_rejects_impure_helpers() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new(&tel);
    let code_id = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/guard_impure.fz".to_string()),
        text: r#"
fn bad(n) do
  if n > 0 do
    true
  else
    false
  end
end
"#
        .to_string(),
    });

    assert_resolved(compiler.drive(), "first drive should index impure helpers");
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should scope impure helpers"
    );
    assert_resolved(compiler.drive(), "second drive should define impure helpers");

    let bad_id = function_id(&capture, "bad", 1);
    assert!(
        compiler.demand(Job::ReifyGuardDispatch(bad_id)),
        "impure helper should still be demandable"
    );
    let outcome = compiler.drive();
    let job = match outcome {
        DriveOutcome::Fatal { job } => job,
        other => panic!("impure helper reification should fail fatally: {other:?}"),
    };
    assert_eq!(
        job,
        Job::ReifyGuardDispatch(bad_id),
        "fatal job should be the demanded impure helper reification"
    );

    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("impure helper diagnostic");
    assert_eq!(
        metadata_str(&diagnostic, "code"),
        codes::LOWER_UNSUPPORTED.0,
        "impure helpers should surface as unsupported guard reification"
    );
    assert!(
        metadata_str(&diagnostic, "message").contains("not dispatch-pure"),
        "impure helper diagnostic should explain the rejected property"
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

    assert_resolved(compiler.drive(), "first drive should index nested module scopes");
    let indexed_outputs = outputs
        .take("IndexCode", code_id.as_u32() as u64)
        .expect("IndexCode job effects");
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
    assert_resolved(
        compiler.drive(),
        "second drive should scope the root module declarations",
    );

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
    assert_resolved(
        compiler.drive(),
        "third drive should define the demanded nested module and its parents",
    );

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

    assert_resolved(compiler.drive(), "first drive should index import-only scope");
    let module_ids = module_indexed_ids(
        &outputs
            .take("IndexCode", code_id.as_u32() as u64)
            .expect("IndexCode job effects"),
    );
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-only scope"
    );
    assert_resolved(compiler.drive(), "second drive should scope import-only modules");
    assert_eq!(
        capture.count(&["fz", "compiler2", "function", "defined"]),
        0,
        "root definition should not eagerly define import-only modules"
    );
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(compiler.drive(), "third drive should define Math before retrying User");
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

    assert_resolved(compiler.drive(), "first drive should index import-only unknown scope");
    let module_ids = module_indexed_ids(
        &outputs
            .take("IndexCode", code_id.as_u32() as u64)
            .expect("IndexCode job effects"),
    );
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-only unknown scope"
    );
    assert_resolved(
        compiler.drive(),
        "second drive should scope import-only unknown modules",
    );
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    let outcome = compiler.drive();
    let job = match outcome {
        DriveOutcome::Fatal { job } => job,
        other => panic!("third drive should fail once Math's defined surface lacks missing/1: {other:?}"),
    };
    assert_eq!(
        job,
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

    assert_resolved(compiler.drive(), "first drive should index import-all scope");
    let module_ids = module_indexed_ids(
        &outputs
            .take("IndexCode", code_id.as_u32() as u64)
            .expect("IndexCode job effects"),
    );
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-all scope"
    );
    assert_resolved(compiler.drive(), "second drive should scope import-all modules");
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(compiler.drive(), "third drive should define Math before retrying User");
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

    assert_resolved(compiler.drive(), "first drive should index import-except scope");
    let module_ids = module_indexed_ids(
        &outputs
            .take("IndexCode", code_id.as_u32() as u64)
            .expect("IndexCode job effects"),
    );
    assert!(
        compiler.demand(Job::ScopeCode(code_id)),
        "explicit demand should enqueue root definition for import-except scope"
    );
    assert_resolved(compiler.drive(), "second drive should scope import-except modules");
    assert!(
        compiler.demand(Job::DefineModule(module_ids[0])),
        "demanding User should enqueue the consumer module only"
    );
    assert_resolved(compiler.drive(), "third drive should define Math before retrying User");
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
    outputs: JobOutputMap,
    spans: SpanJobs,
}

struct GuardDispatchCapture {
    dispatches: GuardDispatchMap,
}

impl OutputCapture {
    fn new() -> Self {
        Self {
            outputs: Rc::new(RefCell::new(HashMap::new())),
            spans: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(OutputCaptureHandler {
            outputs: self.outputs.clone(),
            spans: self.spans.clone(),
        })
    }

    fn take(&self, job_kind: &str, id: u64) -> Option<OutputFacts> {
        let key = (job_kind.to_string(), id);
        let mut outputs = self.outputs.borrow_mut();
        let matches = outputs.get_mut(&key)?;
        let output = matches.pop();
        if matches.is_empty() {
            outputs.remove(&key);
        }
        output
    }
}

impl GuardDispatchCapture {
    fn new() -> Self {
        Self {
            dispatches: Rc::new(RefCell::new(HashMap::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(GuardDispatchCaptureHandler {
            dispatches: self.dispatches.clone(),
        })
    }

    fn take(&self, name: &str, arity: u64) -> Option<PatternGuardDispatch> {
        let key = (name.to_string(), arity);
        let mut dispatches = self.dispatches.borrow_mut();
        let matches = dispatches.get_mut(&key)?;
        let dispatch = matches.pop();
        if matches.is_empty() {
            dispatches.remove(&key);
        }
        dispatch
    }
}

struct OutputCaptureHandler {
    outputs: JobOutputMap,
    spans: SpanJobs,
}

struct GuardDispatchCaptureHandler {
    dispatches: GuardDispatchMap,
}

impl Handler for OutputCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "job"] {
            return;
        }
        match event.kind {
            EventKind::SpanStart => {
                let Some(Value::Str(kind)) = event.metadata.get("kind") else {
                    return;
                };
                let Some(Value::U64(id)) = event.metadata.get("id") else {
                    return;
                };
                self.spans
                    .borrow_mut()
                    .insert(event.span_id, (kind.as_ref().to_string(), *id));
            }
            EventKind::SpanStop => {
                let Some(job_key) = self.spans.borrow_mut().remove(&event.span_id) else {
                    return;
                };
                let Some(effects) = event
                    .metadata
                    .get("effects")
                    .and_then(|value| value.downcast_ref::<JobEffects>())
                else {
                    return;
                };
                self.outputs
                    .borrow_mut()
                    .entry(job_key)
                    .or_default()
                    .push(effects.outputs.clone());
            }
            EventKind::Event | EventKind::SpanException => {}
        }
    }
}

impl Handler for GuardDispatchCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "guard_dispatch", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(Value::Str(name)) = event.metadata.get("name") else {
            return;
        };
        let Some(Value::U64(arity)) = event.measurements.get("arity") else {
            return;
        };
        let Some(dispatch) = event
            .metadata
            .get("dispatch")
            .and_then(|value| value.downcast_ref::<PatternGuardDispatch>())
        else {
            return;
        };
        self.dispatches
            .borrow_mut()
            .entry((name.as_ref().to_string(), *arity))
            .or_default()
            .push(dispatch.clone());
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

fn guard_dispatch(capture: &GuardDispatchCapture, name: &str, arity: u64) -> PatternGuardDispatch {
    capture
        .take(name, arity)
        .unwrap_or_else(|| panic!("guard_dispatch.defined for {name}/{arity}"))
}

fn guard_dispatch_has_nested_dispatch(dispatch: &PatternGuardDispatch) -> bool {
    dispatch.plan.guards.iter().any(expr_has_nested_dispatch) || dispatch.bodies.iter().any(expr_has_nested_dispatch)
}

fn expr_has_nested_dispatch(expr: &PatternGuardExpr) -> bool {
    match expr {
        PatternGuardExpr::Dispatch { .. } => true,
        PatternGuardExpr::Unary { expr, .. } => expr_has_nested_dispatch(expr),
        PatternGuardExpr::Binary { lhs, rhs, .. } => expr_has_nested_dispatch(lhs) || expr_has_nested_dispatch(rhs),
        PatternGuardExpr::Const(_) | PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => false,
    }
}

fn guard_dispatch_has_binary_nested_input(dispatch: &PatternGuardDispatch) -> bool {
    dispatch.bodies.iter().any(expr_has_binary_nested_input)
}

fn expr_has_binary_nested_input(expr: &PatternGuardExpr) -> bool {
    match expr {
        PatternGuardExpr::Dispatch { inputs, dispatch } => {
            inputs
                .iter()
                .any(|input| matches!(input, PatternGuardExpr::Binary { .. }))
                || dispatch.bodies.iter().any(expr_has_binary_nested_input)
                || dispatch.plan.guards.iter().any(expr_has_binary_nested_input)
        }
        PatternGuardExpr::Unary { expr, .. } => expr_has_binary_nested_input(expr),
        PatternGuardExpr::Binary { lhs, rhs, .. } => {
            expr_has_binary_nested_input(lhs) || expr_has_binary_nested_input(rhs)
        }
        PatternGuardExpr::Const(_) | PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => false,
    }
}

fn assert_resolved(outcome: DriveOutcome<Job, ExactPattern<FactKey>>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

fn function_id(capture: &Capture, name: &str, arity: u64) -> FunctionId {
    let event = capture
        .find(&["fz", "compiler2", "function", "defined"])
        .into_iter()
        .find(|event| metadata_str(event, "name") == name && measurement_u64(event, "arity") == arity)
        .unwrap_or_else(|| panic!("function.defined for {name}/{arity}"));
    match event.measurements.get("function_id") {
        Some(Value::U64(id)) => FunctionId::from_u32(*id as u32),
        other => panic!("function_id measurement missing or not u64: {other:?}"),
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
