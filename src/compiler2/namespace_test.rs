use super::{NamespaceSymbol, World};

#[test]
fn compiler2_namespace_store_shadows_and_restores_by_head() {
    let mut world = World::new();
    let kernel = world.modules_mut().define_named("Kernel");
    let dbg_fn = world.functions_mut().define(kernel, "dbg", 1);
    let plus_fn = world.functions_mut().define(kernel, "+", 2);

    let prelude = world
        .namespaces_mut()
        .bind(None, "dbg", NamespaceSymbol::Function(dbg_fn));
    world.namespaces_mut().set_prelude_head(prelude);

    let savepoint = world.namespaces().prelude_head();
    let head = world
        .namespaces_mut()
        .bind(savepoint, "dbg", NamespaceSymbol::Function(plus_fn));
    let head = world
        .namespaces_mut()
        .bind(head, "Kernel", NamespaceSymbol::Module(kernel));

    assert_eq!(
        world.namespaces().lookup(head, "dbg"),
        Some(NamespaceSymbol::Function(plus_fn)),
        "first match should win within the current head"
    );
    assert_eq!(
        world.namespaces().lookup(head, "Kernel"),
        Some(NamespaceSymbol::Module(kernel)),
        "new bindings should resolve immediately"
    );

    let restored = world.namespaces().restore(savepoint);
    assert_eq!(
        world.namespaces().lookup(restored, "dbg"),
        Some(NamespaceSymbol::Function(dbg_fn)),
        "restoring the savepoint should drop shadowing bindings"
    );
    assert_eq!(
        world.namespaces().lookup(restored, "Kernel"),
        None,
        "restoring the savepoint should hide bindings added after it"
    );
}
