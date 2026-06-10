use std::rc::Rc;

use super::quoted_surface::{SurfaceSourceContext, read_compiler_fragment_surface};
use super::source_publish::{ScopePublication, publish_scope};
use super::source_test::quoted_tokens;
use super::{
    DriveOutcome, FactKey, Job, ModuleId, Namespace, NamespaceSymbol, QuotedSourceBuilder, QuotedSourceHeap,
    QuotedSourceMetadata, QuotedSourceRoot, ScopeSnapshot, World,
};
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};

fn meta() -> QuotedSourceMetadata {
    QuotedSourceMetadata::default()
}

fn function_form(
    builder: &QuotedSourceBuilder,
    name: &str,
    body: fz_runtime::any_value::AnyValueRef,
) -> fz_runtime::any_value::AnyValueRef {
    let head = builder.call(name, &meta(), &[]).expect("function head");
    let do_kw = builder.keyword("do", body).expect("do keyword");
    let kw = builder.list(&[do_kw]).expect("function keyword list");
    builder.call("fn", &meta(), &[head, kw]).expect("function form")
}

fn compiler_define_form(
    builder: &QuotedSourceBuilder,
    source: fz_runtime::any_value::AnyValueRef,
    env: fz_runtime::any_value::AnyValueRef,
) -> fz_runtime::any_value::AnyValueRef {
    let compiler = builder.alias(&meta(), &["Fz", "Compiler"]).expect("Fz.Compiler alias");
    let callee_tail = builder
        .list(&[compiler, builder.atom("define")])
        .expect("compiler callee tail");
    let callee = builder
        .ast_node(builder.atom("."), &meta(), callee_tail)
        .expect("compiler define callee");
    builder
        .call_callee(callee, &meta(), &[source, env])
        .expect("compiler define call")
}

fn root_list(builder: &QuotedSourceBuilder, items: &[fz_runtime::any_value::AnyValueRef]) -> QuotedSourceRoot {
    builder
        .root(builder.list(items).expect("quoted root list"))
        .expect("quoted source root")
}

fn measurement_u64(event: &crate::telemetry::capture::OwnedEvent, key: &str) -> u64 {
    match event.measurements.get(key) {
        Some(Value::U64(value)) => *value,
        other => panic!("measurement key `{key}` missing or not u64: {other:?}"),
    }
}

fn metadata_str<'a>(event: &'a crate::telemetry::capture::OwnedEvent, key: &str) -> &'a str {
    match event.metadata.get(key) {
        Some(Value::Str(value)) => value.as_ref(),
        other => panic!("metadata key `{key}` missing or not str: {other:?}"),
    }
}

fn publish_compiler_fragment_scope(
    world: &mut World<'_>,
    code: super::CodeId,
    root: &QuotedSourceRoot,
) -> ScopePublication {
    let ctx = SurfaceSourceContext::new(code, world.code_text(code));
    let surface = read_compiler_fragment_surface(root, &ctx).expect("compiler fragment surface");
    publish_scope(
        world,
        code,
        ScopeSnapshot::module(ModuleId::GLOBAL, Namespace::default()),
        &surface,
    )
    .expect("publish compiler fragment scope")
}

#[test]
fn compiler_service_define_publishes_function_source_and_threads_namespace_forward() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler2"], capture.handler());

    let mut world = World::new(&tel);
    let code = world.submit_code(Some("compiler-service.fz".to_string()), String::new());
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();

    let foo = function_form(&builder, "foo", builder.int(41));
    let service = compiler_define_form(&builder, foo, builder.map(&[]).expect("__ENV__"));
    let bar_body = builder.call("foo", &meta(), &[]).expect("bar calls foo");
    let bar = function_form(&builder, "bar", bar_body);
    let root = root_list(&builder, &[service, bar]);
    let publication = publish_compiler_fragment_scope(&mut world, code, &root);
    let ScopePublication::Complete { outputs, .. } = publication else {
        panic!("compiler-service scope should not block");
    };

    let foo_id = world.reference_function(ModuleId::GLOBAL, "foo", 0);
    let bar_id = world.reference_function(ModuleId::GLOBAL, "bar", 0);
    assert!(
        outputs.iter().any(|(fact, _)| *fact == FactKey::FunctionSource(foo_id)),
        "Fz.Compiler.define should be the source-publication point for foo/0",
    );
    assert!(
        outputs.iter().any(|(fact, _)| *fact == FactKey::FunctionSource(bar_id)),
        "literal function forms should also publish through the compiler-service path",
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "compiler_service", "define"]),
        2,
        "both the explicit service form and the literal function form should cross the compiler-service boundary",
    );
    for event in capture.find(&["fz", "compiler2", "compiler_service", "define"]) {
        assert_eq!(
            metadata_str(&event, "origin"),
            "fz_compiler",
            "all function source publication should use the Fz.Compiler authority",
        );
        assert_ne!(
            measurement_u64(&event, "env_root_ref"),
            0,
            "compiler-service publication should carry a real __ENV__ root",
        );
    }

    let bar_source = world.function_source(bar_id).expect("bar source");
    let foo_source = world.function_source(foo_id).expect("foo source");
    assert_eq!(
        world.lookup_namespace(foo_source.namespace, "foo"),
        Some(NamespaceSymbol::Function(foo_id)),
        "a service-defined function should capture a namespace that includes its own binding",
    );
    assert_eq!(
        world.lookup_namespace(bar_source.namespace, "foo"),
        Some(NamespaceSymbol::Function(foo_id)),
        "the service-updated namespace should be visible to later source forms",
    );
}

#[test]
fn compiler_service_define_and_direct_source_publish_identical_raw_function_facts() {
    let tel = ConfiguredTelemetry::new();
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let foo = function_form(&builder, "foo", builder.int(41));
    let env = builder.map(&[]).expect("__ENV__");

    let mut direct_world = World::new(&tel);
    let direct_code = direct_world.submit_code(Some("direct.fz".to_string()), String::new());
    let direct_root = root_list(&builder, std::slice::from_ref(&foo));
    let direct_publication = publish_compiler_fragment_scope(&mut direct_world, direct_code, &direct_root);

    let mut service_world = World::new(&tel);
    let service_code = service_world.submit_code(Some("service.fz".to_string()), String::new());
    let service_root = root_list(&builder, &[compiler_define_form(&builder, foo, env)]);
    let service_publication = publish_compiler_fragment_scope(&mut service_world, service_code, &service_root);

    let ScopePublication::Complete {
        outputs: direct_outputs,
        ..
    } = direct_publication
    else {
        panic!("direct publication should complete");
    };
    let ScopePublication::Complete {
        outputs: service_outputs,
        ..
    } = service_publication
    else {
        panic!("compiler-service publication should complete");
    };

    let direct_id = direct_world.reference_function(ModuleId::GLOBAL, "foo", 0);
    let service_id = service_world.reference_function(ModuleId::GLOBAL, "foo", 0);
    assert_eq!(
        direct_id, service_id,
        "both entry paths should mint the same function identity"
    );
    assert_eq!(
        direct_outputs.iter().map(|(fact, _)| fact.clone()).collect::<Vec<_>>(),
        service_outputs.iter().map(|(fact, _)| fact.clone()).collect::<Vec<_>>(),
        "direct source and compiler-service publication should emit the same fact keys",
    );

    let direct_source = direct_world.function_source(direct_id).expect("direct function source");
    let service_source = service_world
        .function_source(service_id)
        .expect("service function source");
    assert_eq!(direct_source.owner_module, service_source.owner_module);
    assert_eq!(direct_source.namespace, service_source.namespace);
    assert_eq!(
        direct_source.required_remote_macros,
        service_source.required_remote_macros
    );
    assert_eq!(direct_source.variadic, service_source.variadic);
    assert_eq!(direct_source.source.key(), service_source.source.key());
    assert_eq!(
        world_lookup(&direct_world, direct_source.namespace, "foo"),
        world_lookup(&service_world, service_source.namespace, "foo"),
        "both entry paths should capture the same namespace self-binding",
    );
}

fn world_lookup(world: &World<'_>, namespace: Namespace, name: &str) -> Option<NamespaceSymbol> {
    world.lookup_namespace(namespace, name)
}

#[test]
fn compiler_service_define_groups_single_function_source_before_define_function() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let code = world.submit_code(Some("compiler-service-single.fz".to_string()), String::new());
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();

    let foo = function_form(&builder, "foo", builder.int(42));
    let service = compiler_define_form(&builder, foo, builder.map(&[]).expect("__ENV__"));
    let root = root_list(&builder, &[service]);
    let publication = publish_compiler_fragment_scope(&mut world, code, &root);
    assert!(matches!(publication, ScopePublication::Complete { .. }));

    let foo_id = world.reference_function(ModuleId::GLOBAL, "foo", 0);
    assert!(
        world.demand(Job::DefineFunction(foo_id)),
        "explicit compiler service source should be definable after publication",
    );
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "Fz.Compiler.define should group a single function form before DefineFunction decodes it",
    );
}

#[test]
fn compiler_service_define_inside_a_function_body_has_no_source_publication_authority() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler2"], capture.handler());

    let mut world = World::new(&tel);
    let code = world.submit_code(Some("compiler-service-body.fz".to_string()), String::new());
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();

    let sneaky = function_form(&builder, "sneaky", builder.int(42));
    let body_service = compiler_define_form(&builder, sneaky, builder.map(&[]).expect("__ENV__"));
    let main = function_form(&builder, "main", body_service);
    let root = root_list(&builder, &[main]);
    let publication = publish_compiler_fragment_scope(&mut world, code, &root);
    let ScopePublication::Complete { outputs, .. } = publication else {
        panic!("function-body compiler-service shape should not block source publication");
    };

    let main_id = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let sneaky_id = world.reference_function(ModuleId::GLOBAL, "sneaky", 0);
    assert!(
        outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::FunctionSource(main_id)),
        "the containing function should publish normally",
    );
    assert!(
        !outputs
            .iter()
            .any(|(fact, _)| *fact == FactKey::FunctionSource(sneaky_id)),
        "compiler-service-shaped calls inside runtime bodies must not publish source facts",
    );
    assert!(
        world.function_source(sneaky_id).is_none(),
        "runtime-body calls should not receive source-production authority",
    );
    assert_eq!(
        capture.count(&["fz", "compiler2", "compiler_service", "define"]),
        1,
        "only the literal main/0 source publication should cross the compiler-service boundary",
    );
}

#[test]
fn source_publication_expands_item_macros_as_scope_fragments() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut world = World::new(&tel);
    let code = world.submit_code(
        Some("item-macro.fz".to_string()),
        r#"
defmacro make_answer() do
  source = {:fn, %{}, [{:answer, %{}, []}, [{:do, 42}]]}

  quote do
    Fz.Compiler.define(
      unquote(source),
      unquote(__CALLER__)
    )
  end
end

make_answer()

fn main(), do: answer()
"#
        .to_string(),
    );

    assert!(world.demand(Job::ScopeCode(code)), "code scoping should be demandable");
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "source publication should expand item macros and apply returned source forms",
    );

    let answer = world.reference_function(ModuleId::GLOBAL, "answer", 0);
    let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let make_answer = world.reference_function(ModuleId::GLOBAL, "make_answer", 0);
    assert!(
        world.function_source(answer).is_some(),
        "item macro should publish the function source it returned",
    );
    assert!(
        world.function_source(main).is_some(),
        "later source forms should publish after item macro expansion updates the namespace",
    );
    assert!(
        capture
            .find(&["fz", "compiler2", "macro", "expanded"])
            .into_iter()
            .filter(|event| measurement_u64(event, "function_id") == make_answer.as_u32() as u64)
            .count()
            >= 1,
        "item macro expansion should run through the ordinary macro executable path",
    );
    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "item macro source publication should not invoke the old frontend lowerer",
    );
}

#[test]
fn source_publication_defers_local_macro_expansion_until_function_demand() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "compiler2"], capture.handler());
    let mut world = World::new(&tel);
    let code = world.submit_code(
        Some("macro_inc.fz".to_string()),
        include_str!("../../fixtures/macro_inc/input.fz").to_string(),
    );

    assert!(world.demand(Job::ScopeCode(code)), "code scoping should be demandable");
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "source publication should complete without expanding ordinary function bodies",
    );

    let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let inc = world.reference_function(ModuleId::GLOBAL, "inc", 1);
    let double = world.reference_function(ModuleId::GLOBAL, "double", 1);
    let source = world.function_source(main).expect("main source should be published");
    let tokens = quoted_tokens(&source.source);
    assert!(
        tokens.iter().any(|token| token == "inc") && tokens.iter().any(|token| token == "double"),
        "raw function source should retain macro calls until the function is demanded; tokens={tokens:?}",
    );
    let body_macro_expanded_before = capture
        .find(&["fz", "compiler2", "macro", "expanded"])
        .into_iter()
        .filter(|event| {
            matches!(
                measurement_u64(event, "function_id"),
                id if id == inc.as_u32() as u64 || id == double.as_u32() as u64
            )
        })
        .count();
    assert_eq!(
        body_macro_expanded_before, 0,
        "ScopeCode should not expand body-local macros for an undemanded function",
    );
    assert_eq!(
        capture
            .find(&["fz", "compiler2", "function", "source", "expanded"])
            .into_iter()
            .filter(|event| measurement_u64(event, "function_id") == main.as_u32() as u64)
            .count(),
        0,
        "ScopeCode should not stage expanded function source for an undemanded function",
    );

    assert!(
        world.demand(Job::DefineFunction(main)),
        "the function should be demandable"
    );
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "demanding the function should stage its expanded source and define it",
    );

    let expanded = world
        .expanded_function_source(main)
        .expect("the demanded function should materialize staged expanded source");
    let tokens = quoted_tokens(&expanded.source);
    assert!(
        tokens.iter().any(|token| token == "+") && tokens.iter().any(|token| token == "*"),
        "expanded source should contain the operators returned by the macros; tokens={tokens:?}",
    );
    assert!(
        !tokens.iter().any(|token| token == "inc" || token == "double"),
        "macro calls should not survive in staged expanded function source; tokens={tokens:?}",
    );
    let macro_expanded = capture.find(&["fz", "compiler2", "macro", "expanded"]);
    let body_macro_expanded = macro_expanded
        .iter()
        .filter(|event| {
            matches!(
                measurement_u64(event, "function_id"),
                id if id == inc.as_u32() as u64 || id == double.as_u32() as u64
            )
        })
        .count();
    assert!(
        body_macro_expanded >= 4,
        "demand-time body expansion should emit macro invocation telemetry for the body-local macros",
    );
    let expanded = capture.find(&["fz", "compiler2", "function", "source", "expanded"]);
    let main_expanded = expanded
        .iter()
        .filter(|event| measurement_u64(event, "function_id") == main.as_u32() as u64)
        .count();
    assert_eq!(
        main_expanded, 1,
        "the demanded function should stage its expanded source exactly once",
    );
    for event in macro_expanded {
        assert_eq!(
            measurement_u64(&event, "input_heap_id"),
            measurement_u64(&event, "output_heap_id"),
            "macro expansion should return a new root in the same quoted-source heap",
        );
        assert_ne!(
            measurement_u64(&event, "input_root_ref"),
            0,
            "macro expansion telemetry should identify the source call root",
        );
    }
}

#[test]
fn source_publication_defers_source_sugar_rewrite_until_function_demand() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());
    let mut world = World::new(&tel);
    let code = world.submit_code(
        Some("source-sugar.fz".to_string()),
        r#"
fn main() do
  add = &(&1 + &2)
  classify = fn
    0 -> :zero
    n when n > 0 -> :pos
    _ -> :other
  end
  list = [1, 2] ++ [3] -- [1]
  text = "foo" <> "bar"
  range = 1..5//2
  1 |> case do
    1 -> {add.(20, 22), classify.(0), list, text, range}
  end
end
"#
        .to_string(),
    );

    assert!(
        world.demand(Job::ScopeCode(code)),
        "source scoping should be demandable"
    );
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "source publication should not rewrite source-only sugars inside ordinary functions",
    );

    let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let source = world.function_source(main).expect("main source should be published");
    let tokens = quoted_tokens(&source.source);
    for sugar in ["|>", "&", "++", "--", "<>", "..", "//"] {
        assert!(
            tokens.iter().any(|token| token == sugar),
            "raw FunctionSource should retain source-only sugar `{sugar}` before demand; tokens={tokens:?}",
        );
    }
    assert!(
        world.demand(Job::DefineFunction(main)),
        "the function should be demandable"
    );
    assert!(
        matches!(world.drive(), DriveOutcome::Resolved),
        "demanding the function should rewrite sugars into staged expanded source",
    );
    let expanded = world
        .expanded_function_source(main)
        .expect("the demanded function should materialize staged expanded source");
    let tokens = quoted_tokens(&expanded.source);
    for sugar in ["|>", "&", "++", "--", "<>", "..", "//", "not in"] {
        assert!(
            !tokens.iter().any(|token| token == sugar),
            "expanded function source should not retain source-only sugar `{sugar}`; tokens={tokens:?}",
        );
    }
    for rewritten in [
        "case",
        "List",
        "concat",
        "subtract",
        "Kernel",
        "fz_binary_concat",
        "Range",
        "new",
    ] {
        assert!(
            tokens.iter().any(|token| token == rewritten),
            "expanded function source should contain rewritten form token `{rewritten}`; tokens={tokens:?}",
        );
    }
    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "source publication must not invoke the old frontend lowerer",
    );
}
