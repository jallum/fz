use std::rc::Rc;

use super::env_projection::CallSite;
use super::quoted_expander::ExpansionContext;
use super::quoted_surface::ScopeSurface;
use super::{Job, ModuleId, NamespaceSymbol, QuotedSourceHeap, ScopeSnapshot, World};
use crate::telemetry::ConfiguredTelemetry;

#[test]
fn compiler2_impl_environment_projects_the_impl_modules_atom() {
    use crate::modules::identity::ModuleName;
    let mut world = World::new();
    let protocol = world.reference_module(ModuleName::parse_dotted("A").unwrap());
    let target = world.reference_module(ModuleName::parse_dotted("B.C").unwrap());
    let owner = world.reference_protocol_impl_module(protocol, target);
    let scope = ScopeSnapshot::module(owner, world.prelude_head());
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let site = CallSite::locate(None, &world.source_map().borrow());
    let env = builder
        .root(
            world
                .project_env_value(&builder, scope, ExpansionContext::Expression, &site)
                .unwrap(),
        )
        .unwrap();
    let module = env.cursor().map_value("module").unwrap().unwrap();
    assert_eq!(module.atom_name().unwrap().to_string(), "Elixir.A.B.C");
    assert_eq!(
        world.reference_module(ModuleName::parse_dotted("A.B.C").unwrap()),
        owner,
        "the atom `A.B.C` names the impl module: one atom, one module"
    );
}

#[test]
fn compiler2_scope_snapshot_projects_module_atom_and_env_from_one_authority() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let module = world.reference_module(crate::modules::identity::ModuleName::parse_dotted("App.Tools").unwrap());
    let function = world.reference_function(module, "run", 2);
    let namespace = world.bind_namespace(world.prelude_head(), "Tools", NamespaceSymbol::Module(module));
    let scope = ScopeSnapshot::function(module, namespace, function);

    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();

    let module_atom = builder
        .root(world.module_atom_value(&builder, scope.module_id()))
        .expect("module root");
    assert_eq!(
        module_atom.cursor().atom_name().expect("module atom").to_string(),
        "Elixir.App.Tools",
        "__MODULE__ should project from the current module identity, not from bare namespace state",
    );

    let site = CallSite::locate(None, &world.source_map().borrow());
    let env_root = builder
        .root(
            world
                .project_env_value(&builder, scope, ExpansionContext::Expression, &site)
                .expect("project __ENV__"),
        )
        .expect("env root");
    let env = env_root.cursor();
    let env_module = env
        .map_value("module")
        .expect("env module lookup")
        .expect("env module value");
    assert_eq!(
        env_module.atom_name().expect("env module atom").to_string(),
        "Elixir.App.Tools",
        "__ENV__.module is the same atom as __MODULE__",
    );

    let env_function = env
        .map_value("function")
        .expect("env function lookup")
        .expect("env function value")
        .tuple_items()
        .expect("env function tuple");
    assert_eq!(env_function[0].atom_name().expect("function name"), "run");
    assert_eq!(env_function[1].int_value().expect("function arity"), 2);
}

#[test]
fn compiler2_module_scope_returns_a_scope_snapshot_not_just_a_namespace() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let code = world.submit_code(
        Some("scoped.fz".to_string()),
        include_str!("../../fixtures2/00050_empty.fz").to_string(),
    );
    assert!(matches!(
        super::drive::ExecutionContext::new(&mut world, &tel).drive(),
        fz_engine::DriveOutcome::Resolved
    ));

    let module = world.reference_module(crate::modules::identity::ModuleName::parse_dotted("Scoped").unwrap());
    let parent = world.reference_module(crate::modules::identity::ModuleName::parse_dotted("Parent").unwrap());
    let namespace = world.bind_namespace(world.prelude_head(), "Parent", NamespaceSymbol::Module(parent));
    world.index_module_body(
        module,
        code,
        ModuleId::GLOBAL,
        super::QuotedSourceRoot::empty(),
        crate::source::Span::DUMMY,
        ScopeSurface {
            attrs: Vec::new(),
            forms: Vec::new(),
        },
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
    let mut world = World::new();
    let code = world.submit_code(
        Some("app.fz".to_string()),
        include_str!("../../fixtures2/00051_module_app_run.fz").to_string(),
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            fz_engine::DriveOutcome::Resolved
        ),
        "indexing should resolve before scoping"
    );
    assert!(world.demand(Job::ScopeCode(code)), "code scope should be demandable");
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            fz_engine::DriveOutcome::Resolved
        ),
        "top-level scope should resolve"
    );

    let app = world.reference_module(crate::modules::identity::ModuleName::parse_dotted("App").unwrap());
    assert!(
        world.demand(Job::DefineModule(app)),
        "module definition should be demandable"
    );
    assert!(
        matches!(
            super::drive::ExecutionContext::new(&mut world, &tel).drive(),
            fz_engine::DriveOutcome::Resolved
        ),
        "module definition should resolve"
    );

    let run = world.reference_function(app, "run", 1);
    let scope = world.function_scope(run).expect("defined function scope");

    assert_eq!(scope.module_id(), app);
    assert_eq!(scope.function_id(), Some(run));
}
