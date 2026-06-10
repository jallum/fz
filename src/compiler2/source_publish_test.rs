use std::rc::Rc;

use super::quoted_surface::{SurfaceSourceContext, read_scope_surface};
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
    let ctx = SurfaceSourceContext::new(code, world.code_text(code), world.tel());
    let surface = read_scope_surface(&root, &ctx).expect("source surface with compiler service");

    let publication = publish_scope(
        &mut world,
        code,
        ScopeSnapshot::module(ModuleId::GLOBAL, Namespace::default()),
        &surface,
    )
    .expect("publish source scope");
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
    let ctx = SurfaceSourceContext::new(code, world.code_text(code), world.tel());
    let surface = read_scope_surface(&root, &ctx).expect("source surface");

    let publication = publish_scope(
        &mut world,
        code,
        ScopeSnapshot::module(ModuleId::GLOBAL, Namespace::default()),
        &surface,
    )
    .expect("publish source scope");
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
fn source_publication_expands_local_macros_before_saving_function_source() {
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
        "source publication should drive local macro executables and resume scoping",
    );

    let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let source = world.function_source(main).expect("main source should be published");
    let tokens = quoted_tokens(&source.source);
    assert!(
        tokens.iter().any(|token| token == "+") && tokens.iter().any(|token| token == "*"),
        "expanded source should contain the operators returned by the macros; tokens={tokens:?}",
    );
    assert!(
        !tokens.iter().any(|token| token == "inc" || token == "double"),
        "macro calls should not be saved in FunctionSource after expansion; tokens={tokens:?}",
    );
    let expanded = capture.find(&["fz", "compiler2", "macro", "expanded"]);
    assert!(
        expanded.len() >= 4,
        "recursive expansion should emit macro invocation telemetry",
    );
    for event in expanded {
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
