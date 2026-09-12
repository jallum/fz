//! Macro source consumers read the same retained product authority as runtime roots.

use std::cell::RefCell;
use std::rc::Rc;

use crate::exec::runtime::ProcessExitCapture;
use crate::telemetry::ConfiguredTelemetry;

use super::pull::{ProductKey, ProductRequestId, PullOutcome};
use super::{CodeSubmission, Compiler2, ExecutableNeed, Job, ModuleId, QuotedSourceRoot, RootSubmission, World};

#[test]
fn body_macro_caller_uses_the_definition_function_and_source_namespace() {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let expansions = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&expansions);
    tel.attach_raw_event3::<World, super::FunctionId, QuotedSourceRoot, _>(
        &["fz", "compiler2", "macro", "expanded"],
        move |_, _, _, _, function, _| observed.borrow_mut().push(*function),
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_cache_caller_scope.fz".into()),
        text: "defmacro caller_function() do\n quote do: unquote(__CALLER__.function) == {:main, 0}\nend\ndefmacro caller_namespace() do\n quote do: unquote(__CALLER__.namespace) + 0\nend\ndef main() do\n assert(caller_function(), \"caller function\")\n caller_namespace()\nend\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let caller_function = compiler
        .world_mut()
        .reference_function(ModuleId::GLOBAL, "caller_function", 0);
    let caller_namespace = compiler
        .world_mut()
        .reference_function(ModuleId::GLOBAL, "caller_namespace", 0);

    let result = compiler.run_root_interp(root);
    let main = compiler.root_function(root);
    let source_namespace = compiler
        .world()
        .function_scope(main)
        .expect("main should have an authoritative definition scope")
        .namespace()
        .as_u32() as i64;
    assert_eq!(result, Ok(source_namespace), "{:?}", diagnostics.events());
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|function| **function == caller_function || **function == caller_namespace)
            .count(),
        2,
        "each caller-reflecting macro should execute once despite body-expansion retries"
    );
}

#[test]
fn pipe_rewrite_keeps_macro_invocation_identity_across_nested_product_waits() {
    let tel = ConfiguredTelemetry::new();
    let expansions = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&expansions);
    tel.attach_raw_event3::<World, super::FunctionId, QuotedSourceRoot, _>(
        &["fz", "compiler2", "macro", "expanded"],
        move |_, _, _, _, function, _| observed.borrow_mut().push(*function),
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_cache_source_sugar.fz".into()),
        text: "defmacro outer(x) do\n quote do: inner(unquote(x))\nend\ndefmacro inner(x) do\n quote do: unquote(x) + 1\nend\ndef main(), do: 41 |> outer()\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let outer = compiler.world_mut().reference_function(ModuleId::GLOBAL, "outer", 1);
    let inner = compiler.world_mut().reference_function(ModuleId::GLOBAL, "inner", 1);

    assert_eq!(compiler.run_root_interp(root), Ok(42));
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|function| **function == outer)
            .count(),
        1,
        "rewriting the pipe again on retry must not create a new outer invocation"
    );
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|function| **function == inner)
            .count(),
        1
    );
}

#[test]
fn capture_rewrite_keeps_nested_macro_invocation_identity_across_product_waits() {
    let tel = ConfiguredTelemetry::new();
    let expansions = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&expansions);
    tel.attach_raw_event3::<World, super::FunctionId, QuotedSourceRoot, _>(
        &["fz", "compiler2", "macro", "expanded"],
        move |_, _, _, _, function, _| observed.borrow_mut().push(*function),
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_cache_capture_rewrite.fz".into()),
        text: "defmacro outer(x) do\n quote do: inner(unquote(x))\nend\ndefmacro inner(x) do\n quote do: unquote(x) + 1\nend\ndef main() do\n fun = &(outer(&1))\n fun.(41)\nend\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let outer = compiler.world_mut().reference_function(ModuleId::GLOBAL, "outer", 1);
    let inner = compiler.world_mut().reference_function(ModuleId::GLOBAL, "inner", 1);

    assert_eq!(compiler.run_root_interp(root), Ok(42));
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|function| **function == outer)
            .count(),
        1,
        "retrying capture desugaring must reuse its synthesized outer invocation"
    );
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|function| **function == inner)
            .count(),
        1
    );
}

#[test]
fn macro_expansion_cache_reuses_unchanged_calls_and_invalidates_changed_inputs() {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let expansions = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&expansions);
    tel.attach_raw_event3::<World, super::FunctionId, QuotedSourceRoot, _>(
        &["fz", "compiler2", "macro", "expanded"],
        move |_, _, _, _, function, _| observed.borrow_mut().push(*function),
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_cache_provider.fz".into()),
        text: "defmodule Helpers do\n defmacro inc(x) do\n  quote do: unquote(x) + 1\n end\nend\n".into(),
    });
    compiler.submit_code(CodeSubmission {
        name: Some("macro_cache_initial.fz".into()),
        text: "require Helpers\ndef main(), do: Helpers.inc(40)\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let helpers = compiler
        .world_mut()
        .reference_module(crate::modules::identity::ModuleName::parse_dotted("Helpers").unwrap());
    let inc = compiler.world_mut().reference_function(helpers, "inc", 1);

    assert_eq!(compiler.run_root_interp(root), Ok(41));
    assert_eq!(
        expansions.borrow().iter().filter(|function| **function == inc).count(),
        1
    );

    assert_eq!(compiler.run_root_interp(root), Ok(41));
    assert_eq!(
        expansions.borrow().iter().filter(|function| **function == inc).count(),
        1,
        "an unchanged call and macro product must reuse the immediate expansion"
    );

    compiler.submit_code(CodeSubmission {
        name: Some("macro_cache_changed_input.fz".into()),
        text: "require Helpers\ndef main(), do: Helpers.inc(41)\n".into(),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(42), "{:?}", diagnostics.events());
    assert_eq!(
        expansions.borrow().iter().filter(|function| **function == inc).count(),
        2,
        "a new quoted invocation must execute independently"
    );
}

fn run_macro_program(text: String) -> Result<i64, String> {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("hostile-macro-span.fz".into()),
        text,
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.run_root_interp(root)
}

fn run_macro_with_span_metadata(span_entries: &str) -> Result<i64, String> {
    run_macro_program(format!(
        "def answer(), do: 42\ndefmacro forged() do\n  {{:answer, %{{__fz_span__: %{{{span_entries}}}}}, []}}\nend\ndef main(), do: forged()\n"
    ))
}

#[test]
fn macro_expansion_rejects_negative_quoted_span_offsets() {
    assert!(
        run_macro_with_span_metadata("start: -1, length: 1, source_version: 0").is_err(),
        "malformed quoted provenance must not disappear into a fallback span"
    );
}

#[test]
fn macro_expansion_rejects_unregistered_quoted_source_versions() {
    assert!(
        run_macro_with_span_metadata("start: 0, length: 1, source_version: 4294967294").is_err(),
        "integer-shaped provenance must resolve through the authoritative source map"
    );
}

#[test]
fn macro_expansion_rejects_malformed_nested_cond_clause_provenance() {
    assert!(
        run_macro_program(
            r#"
defmacro forged() do
  clause = {:"->", %{__fz_span__: %{start: -1, length: 1, source_version: 0}}, [[true], 42]}
  {:cond, %{}, [[{:do, [clause]}]]}
end

def main(), do: forged()
"#
            .into(),
        )
        .is_err(),
        "every structurally consumed AST wrapper must validate its own provenance"
    );
}

#[test]
fn macro_expansion_rejects_malformed_nested_remote_callee_provenance() {
    assert!(
        run_macro_program(
            r#"
defmacro forged() do
  callee = {:., %{__fz_span__: %{start: -1, length: 1, source_version: 0}}, [{:__aliases__, %{}, [:Kernel]}, :+]}
  {callee, %{}, [20, 22]}
end

def main(), do: forged()
"#
            .into(),
        )
        .is_err(),
        "nested callable wrappers must cross the same validated AST boundary"
    );
}

#[test]
fn source_less_item_macro_output_round_trips_without_fabricated_provenance() {
    let tel = ConfiguredTelemetry::new();
    let exits = ProcessExitCapture::new();
    exits.install(&tel);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("source-less-item-macro.fz".into()),
        text: r#"
defmacro make_answer() do
  generated = {:generated, %{}, nil}
  quoted = {:quote, %{}, [[{:do, generated}]]}
  source = {:def, %{}, [{:answer, %{}, []}, [{:do, quoted}]]}
  quote do: Fz.Compiler.define(unquote(source), unquote(__CALLER__))
end

make_answer()
def main() do
  {_, meta, _} = answer()
  if meta == %{}, do: 42, else: 0
end
"#
        .into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_eq!(compiler.run_root_interp(root), Ok(42));
    compiler.run_root_jit(root).expect("native source-less quote execution");
    assert_eq!(
        exits.last().expect("native source-less quote exit").halt_value,
        42,
        "interpreter and native quote construction must both omit absent span metadata"
    );
}

#[test]
fn macro_expansion_retains_definition_and_caller_source_versions_per_node() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    let definition_owner = compiler.submit_code(CodeSubmission {
        name: Some("definition.fz".into()),
        text: "defmodule Helpers do\n  defmacro inc(x) do\n    quote do: unquote(x) + 1\n  end\nend\n".into(),
    });
    let caller_owner = compiler.submit_code(CodeSubmission {
        name: Some("caller.fz".into()),
        text: "require Helpers\ndef main(), do: Helpers.inc(40 + 1)\n".into(),
    });
    let definition_version = compiler
        .world()
        .source_version(definition_owner)
        .expect("macro definition version");
    let caller_version = compiler
        .world()
        .source_version(caller_owner)
        .expect("macro caller version");
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_eq!(compiler.run_root_interp(root), Ok(42));
    let main = compiler.root_function(root);
    assert_eq!(
        compiler.world().function_definition(main).0.owner,
        caller_owner,
        "body-macro expansion must retain the caller's lexical publishing owner"
    );
    let expanded = compiler
        .world()
        .expanded_function_source(main)
        .expect("demanded function retains expanded source");
    let source_map = compiler.world().source_map();
    let surface = super::quoted_function::derive_function_surface(&expanded.source, &source_map.borrow())
        .expect("expanded function source remains decodable");
    let crate::ast::Expr::BinOp(_, left, right) = &surface.clauses[0].body.node else {
        panic!("macro result should be the quoted addition");
    };

    assert_eq!(surface.clauses[0].body.span.source_version, definition_version);
    assert_eq!(left.span.source_version, caller_version);
    assert_eq!(right.span.source_version, definition_version);
    assert_ne!(surface.clauses[0].body.span.source_version, left.span.source_version);
}

#[test]
fn repeated_macro_generated_lambdas_keep_distinct_structural_occurrences() {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("source-less-lambda-macro.fz".into()),
        text: r#"
defmacro deferred(x) do
  {:fn, %{}, [{:"->", %{}, [[], x]}]}
end

def main() do
  left = deferred(20)
  right = deferred(22)
  left.() + right.()
end
"#
        .into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(
        compiler.run_root_interp(root),
        Ok(42),
        "two expansions of one definition-site lambda are distinct occurrences in the final owner"
    );
    let main = compiler.root_function(root);
    let super::LoweredBody::Clauses { generated, .. } = compiler.world().lowered_body(main) else {
        panic!("main must lower to source clauses");
    };
    assert_eq!(generated.len(), 2);
    assert_ne!(generated[0], generated[1]);
    let origins = generated
        .iter()
        .map(|function| {
            let super::identity::FunctionOrigin::Generated { owner, occurrence } =
                &compiler.world().function_ref(*function).origin
            else {
                panic!("lambda has typed occurrence");
            };
            assert!(std::sync::Arc::ptr_eq(
                owner,
                &compiler.world().function_ref(main).denotation
            ));
            *occurrence
        })
        .collect::<Vec<_>>();
    assert!(
        generated
            .iter()
            .all(|function| compiler.world().function_surface(*function).span.is_dummy()),
        "source-less expansions share absent diagnostic location"
    );
    assert_eq!(
        [origins[0].as_u32(), origins[1].as_u32()],
        [0, 1],
        "final structural traversal disambiguates equal-range peers before FunctionId allocation"
    );
}

#[test]
fn replacing_a_macro_with_an_ordinary_function_rejects_its_captured_macro_use() {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_before_replacement.fz".into()),
        text: "defmacro answer() do\n quote do: 40 + 1\nend\ndef main(), do: answer()\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(41));
    let replacement = compiler.submit_code(CodeSubmission {
        name: Some("ordinary_replacement.fz".into()),
        text: "def answer(), do: 42\n".into(),
    });
    assert!(compiler.run_root_interp(root).is_err());
    let events = diagnostics.events();
    let diagnostic = events.iter().find_map(|event| event.diagnostic.as_ref()).unwrap();
    assert_eq!(diagnostic.code, crate::diag::codes::LOWER_UNSUPPORTED);
    assert!(diagnostic.message.contains("not a macro"), "{}", diagnostic.message);
    assert_eq!(
        diagnostic.primary.span.source_version,
        compiler
            .world()
            .source_version(replacement)
            .expect("replacement source version")
    );
    assert_eq!((diagnostic.primary.span.start, diagnostic.primary.span.end), (0, 21));
}

#[test]
fn failed_macro_product_remains_demanded_after_retirement_and_source_repair() {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let mut compiler = Compiler2::new(tel);
    let failed_code = compiler.submit_code(CodeSubmission {
        name: Some("macro_product_missing_remote.fz".into()),
        text: "defmacro answer() do\n quote do: unquote(Missing.value())\nend\ndef main(), do: answer()\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        compiler.run_root_interp(root).is_err(),
        "an absent macro dependency cannot certify expanded source"
    );
    let events = diagnostics.events();
    let diagnostic = events.iter().find_map(|event| event.diagnostic.as_ref()).unwrap();
    assert_eq!(diagnostic.code, crate::diag::codes::LOWER_UNBOUND);
    assert_eq!(
        diagnostic.primary.span.source_version,
        compiler
            .world()
            .source_version(failed_code)
            .expect("failed source version")
    );
    assert_eq!((diagnostic.primary.span.start, diagnostic.primary.span.end), (40, 53));
    let function = compiler.world_mut().reference_function(ModuleId::GLOBAL, "answer", 0);
    let macro_root = compiler.world_mut().macro_root(function);
    assert_eq!(
        compiler.retained_product_generation(macro_root, &ProductKey::RootBackendProduct(macro_root)),
        None
    );
    assert!(compiler.retire_root_products(macro_root));
    compiler.submit_code(CodeSubmission {
        name: Some("macro_product_repaired.fz".into()),
        text: "defmacro answer() do\n quote do: 40 + 2\nend\n".into(),
    });
    assert_eq!(
        compiler.run_root_interp(root),
        Ok(42),
        "the exact failed product demand must survive until its dependency can be produced: {:?}",
        diagnostics.events()
    );
    assert_eq!(
        compiler.retained_product_generation(macro_root, &ProductKey::RootBackendProduct(macro_root)),
        Some(1)
    );
}

#[test]
fn macro_content_movement_reexecutes_only_source_consumers_of_changed_content() {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let jobs = Rc::new(RefCell::new(Vec::<Job>::new()));
    let evaluations = Rc::new(RefCell::new(Vec::<ProductKey>::new()));
    let expansions = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&jobs);
    tel.attach_raw_event2::<World, super::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _, completion| observed.borrow_mut().push(completion.job.clone()),
    );
    let observed = Rc::clone(&evaluations);
    tel.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
        &["fz", "compiler2", "pull", "product", "evaluated"],
        move |_, _, _, key, _, _| observed.borrow_mut().push(key.clone()),
    );
    let observed = Rc::clone(&expansions);
    tel.attach_raw_event3::<World, super::FunctionId, QuotedSourceRoot, _>(
        &["fz", "compiler2", "macro", "expanded"],
        move |_, _, _, _, function, _| observed.borrow_mut().push(*function),
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_product_initial.fz".into()),
        text: "def offset(), do: 1\ndefmacro inc(x) do\n quote do: unquote(x) + unquote(offset())\nend\ndef main(), do: inc(40)\ndef control_offset(), do: 3\ndefmacro control_inc(x) do\n quote do: unquote(x) + unquote(control_offset())\nend\ndef control(), do: control_inc(40)\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(41), "{:?}", diagnostics.events());
    let main = compiler.root_function(root);
    let function = compiler.world_mut().reference_function(ModuleId::GLOBAL, "inc", 1);
    let macro_root = compiler.world_mut().macro_root(function);
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|expanded| **expanded == function)
            .count(),
        1
    );
    let content = ProductKey::RootBackendProduct(macro_root);
    let generation = compiler.retained_product_generation(macro_root, &content);
    assert_eq!(generation, Some(1));
    let program = compiler.retained_backend_program(macro_root);
    let source_consumer = Job::ExpandFunctionSource(main);
    let control_root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "control".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(control_root), Ok(43));
    let control_consumer = Job::ExpandFunctionSource(compiler.root_function(control_root));
    let control_function = compiler
        .world_mut()
        .reference_function(ModuleId::GLOBAL, "control_inc", 1);
    let control_macro_root = compiler.world_mut().macro_root(control_function);
    let control_content = ProductKey::RootBackendProduct(control_macro_root);
    let control_generation = compiler.retained_product_generation(control_macro_root, &control_content);
    let control_program = compiler.retained_backend_program(control_macro_root);

    jobs.borrow_mut().clear();
    evaluations.borrow_mut().clear();
    assert_eq!(compiler.run_root_interp(root), Ok(41));
    assert!(
        evaluations.borrow().is_empty(),
        "unchanged macro calls reuse the settled root without compiler evaluation"
    );
    assert!(jobs.borrow().is_empty());
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|expanded| **expanded == function)
            .count(),
        1
    );

    compiler.submit_code(CodeSubmission {
        name: Some("macro_product_unrelated.fz".into()),
        text: "def unrelated(), do: 99\n".into(),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(41));
    assert!(
        evaluations.borrow().is_empty(),
        "unrelated source cannot dirty the macro root"
    );
    assert!(!jobs.borrow().contains(&source_consumer));
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|expanded| **expanded == function)
            .count(),
        1
    );

    jobs.borrow_mut().clear();
    evaluations.borrow_mut().clear();
    compiler.reproduce_job_for_test(Job::SeedRoot(macro_root), vec![super::FactKey::RootEntry(macro_root)]);
    assert_eq!(compiler.run_root_interp(root), Ok(41), "{:?}", diagnostics.events());
    assert!(
        evaluations
            .borrow()
            .contains(&ProductKey::RootBackendProduct(macro_root)),
        "invalidating the exact root prerequisite must reproduce backend content from the same source snapshot"
    );
    assert_eq!(compiler.retained_product_generation(macro_root, &content), generation);
    assert!(Rc::ptr_eq(&program, &compiler.retained_backend_program(macro_root)));
    assert!(
        !jobs.borrow().contains(&source_consumer),
        "equal backend reproduction must restore source finality without executing its consumer"
    );
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|expanded| **expanded == function)
            .count(),
        1,
        "reproducing equal retained content must preserve the macro expansion"
    );

    jobs.borrow_mut().clear();
    evaluations.borrow_mut().clear();
    compiler.submit_code(CodeSubmission {
        name: Some("macro_product_changed.fz".into()),
        text: "def offset(), do: 2\n".into(),
    });
    assert_eq!(
        compiler.run_root_interp(root),
        Ok(42),
        "changed compile-time content must invalidate the exact source reader before runtime consumption"
    );
    assert_eq!(compiler.retained_product_generation(macro_root, &content), Some(2));
    assert_eq!(jobs.borrow().iter().filter(|job| **job == source_consumer).count(), 1);
    assert!(evaluations.borrow().contains(&content));
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|expanded| **expanded == function)
            .count(),
        2,
        "changed retained macro content must execute the invocation once more"
    );
    assert!(!jobs.borrow().contains(&control_consumer));
    assert!(!evaluations.borrow().contains(&control_content));
    assert_eq!(
        compiler.retained_product_generation(control_macro_root, &control_content),
        control_generation
    );
    assert!(Rc::ptr_eq(
        &control_program,
        &compiler.retained_backend_program(control_macro_root)
    ));
    jobs.borrow_mut().clear();
    evaluations.borrow_mut().clear();
    assert_eq!(compiler.run_root_interp(control_root), Ok(43));
    assert!(jobs.borrow().is_empty());
    assert!(evaluations.borrow().is_empty());

    let retained = compiler.retained_backend_program(macro_root);
    let released = Rc::downgrade(&retained);
    drop(retained);
    assert_eq!(compiler.world().macro_expansion_count(function), 1);
    assert!(compiler.retire_root_products(macro_root));
    assert_eq!(
        compiler.world().macro_expansion_count(function),
        0,
        "retiring the macro root must release its cached quoted outputs"
    );
    assert!(
        released.upgrade().is_none(),
        "no World mirror may keep a retired macro backend alive"
    );
    assert_eq!(
        compiler.run_root_interp(root),
        Ok(42),
        "retiring a consumed macro product withdraws its dependency and a later request reproduces it"
    );
    assert_eq!(
        expansions
            .borrow()
            .iter()
            .filter(|expanded| **expanded == function)
            .count(),
        3,
        "reprovisioning a retired macro backend must execute the invocation against the new product"
    );
}
