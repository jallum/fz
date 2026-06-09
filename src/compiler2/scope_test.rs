use std::rc::Rc;

use super::{
    Job, ModuleId, NamespaceSymbol, QuotedLexicalContextKind, QuotedSourceCarrier, QuotedSourceHeap, ScopeSnapshot,
    World,
};
use crate::telemetry::ConfiguredTelemetry;

#[test]
fn compiler2_scope_snapshot_projects_module_alias_and_env_from_one_authority() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let module = world.reference_module("App.Tools");
    let function = world.reference_function(module, "run", 2);
    let namespace = world.bind_namespace(world.prelude_head(), "Tools", NamespaceSymbol::Module(module));
    let scope = ScopeSnapshot::function(module, namespace, function);

    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();

    let module_root = builder
        .root(
            world
                .project_module_value(&builder, scope, QuotedLexicalContextKind::Definition)
                .expect("project __MODULE__"),
        )
        .expect("module root");
    let module_alias = module_root
        .cursor()
        .ast_node()
        .expect("module alias cursor")
        .expect("module alias node");
    assert_eq!(module_alias.head.atom_name().expect("module alias head"), "__aliases__");
    assert_eq!(
        module_alias.tail.list_atom_names().expect("module alias segments"),
        vec!["App".to_string(), "Tools".to_string()],
        "__MODULE__ should project from the current module identity, not from bare namespace state",
    );

    let env_root = builder
        .root(
            world
                .project_env_value(&builder, scope, QuotedLexicalContextKind::Definition)
                .expect("project __ENV__"),
        )
        .expect("env root");
    let env = env_root.cursor();
    let env_module = env
        .map_value("module")
        .expect("env module lookup")
        .expect("env module value")
        .ast_node()
        .expect("env module cursor")
        .expect("env module node");
    assert_eq!(env_module.head.atom_name().expect("env module head"), "__aliases__");
    assert_eq!(
        env_module.tail.list_atom_names().expect("env module alias segments"),
        vec!["App".to_string(), "Tools".to_string()],
        "__ENV__.module should reuse the same authoritative module projection",
    );

    let env_function = env
        .map_value("function")
        .expect("env function lookup")
        .expect("env function value")
        .tuple_items()
        .expect("env function tuple");
    assert_eq!(env_function[0].atom_name().expect("function name"), "run");
    assert_eq!(env_function[1].int_value().expect("function arity"), 2);
    assert_eq!(
        env.map_value("namespace")
            .expect("env namespace lookup")
            .expect("env namespace value")
            .int_value()
            .expect("namespace integer"),
        scope.namespace().as_u32() as i64,
        "__ENV__.namespace should carry the current namespace transport handle",
    );
}

#[test]
fn compiler2_module_scope_returns_a_scope_snapshot_not_just_a_namespace() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let code = world.submit_code(Some("scoped.fz".to_string()), String::new());
    assert!(matches!(world.drive(), super::DriveOutcome::Resolved));

    let module = world.reference_module("Scoped");
    let parent = world.reference_module("Parent");
    let namespace = world.bind_namespace(world.prelude_head(), "Parent", NamespaceSymbol::Module(parent));
    world.index_module_body(
        module,
        code,
        ModuleId::GLOBAL,
        "Scoped".to_string(),
        QuotedSourceCarrier::empty(),
        Vec::new(),
        Vec::new(),
    );
    world.scope_module(module, namespace);

    let (_source, scope) = world.module_scope(module).expect("scoped module snapshot");
    assert_eq!(scope.module_id(), module);
    assert_eq!(scope.namespace(), namespace);
    assert_eq!(scope.function_id(), None);
}

#[test]
fn compiler2_source_scoping_threads_function_scope_through_module_definition() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new(&tel);
    let code = world.submit_code(
        Some("app.fz".to_string()),
        "defmodule App do\n  fn run(x), do: x\nend\n".to_string(),
    );
    assert!(
        matches!(world.drive(), super::DriveOutcome::Resolved),
        "indexing should resolve before scoping"
    );
    assert!(world.demand(Job::ScopeCode(code)), "code scope should be demandable");
    assert!(
        matches!(world.drive(), super::DriveOutcome::Resolved),
        "top-level scope should resolve"
    );

    let app = world.reference_module("App");
    assert!(
        world.demand(Job::DefineModule(app)),
        "module definition should be demandable"
    );
    assert!(
        matches!(world.drive(), super::DriveOutcome::Resolved),
        "module definition should resolve"
    );

    let run = world.reference_function(app, "run", 1);
    let scope = world.function_scope(run).expect("defined function scope");
    let lexical = world.scope_lexical_context(scope, QuotedLexicalContextKind::Definition);

    assert_eq!(scope.module_id(), app);
    assert_eq!(scope.function_id(), Some(run));
    assert_eq!(
        lexical.module,
        vec!["App".to_string()],
        "function lexical context should carry the owning module path",
    );
    assert_eq!(
        lexical.scope,
        vec!["run".to_string()],
        "function lexical context should carry the function name from the same scope snapshot",
    );
    assert_eq!(lexical.namespace_id, Some(scope.namespace().as_u32()));
}
