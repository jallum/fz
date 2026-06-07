use super::{NamespaceSymbol, World};

#[test]
fn compiler2_namespace_store_shadows_and_restores_by_head() {
    let mut world = World::new();
    let code_id = world.code_mut().define(Some("kernel.fz".to_string()), String::new());
    let kernel = world.modules_mut().reference_named("Kernel");
    let _ = world.modules_mut().define(kernel, code_id, None);
    let dbg_fn = world.functions_mut().reference(Some(kernel), "dbg", 1);
    let plus_fn = world.functions_mut().reference(Some(kernel), "+", 2);

    let prelude = world
        .namespaces_mut()
        .bind(None, "dbg", NamespaceSymbol::Functions(vec![dbg_fn]));
    world.namespaces_mut().set_prelude_head(prelude);

    let savepoint = world.namespaces().prelude_head();
    let head = world
        .namespaces_mut()
        .bind(savepoint, "dbg", NamespaceSymbol::Functions(vec![plus_fn]));
    let head = world
        .namespaces_mut()
        .bind(head, "Kernel", NamespaceSymbol::Module(kernel));

    assert_eq!(
        world.namespaces().lookup(head, "dbg"),
        Some(&NamespaceSymbol::Functions(vec![plus_fn])),
        "first match should win within the current head"
    );
    assert_eq!(
        world.namespaces().lookup(head, "Kernel"),
        Some(&NamespaceSymbol::Module(kernel)),
        "new bindings should resolve immediately"
    );

    let restored = world.namespaces().restore(savepoint);
    assert_eq!(
        world.namespaces().lookup(restored, "dbg"),
        Some(&NamespaceSymbol::Functions(vec![dbg_fn])),
        "restoring the savepoint should drop shadowing bindings"
    );
    assert_eq!(
        world.namespaces().lookup(restored, "Kernel"),
        None,
        "restoring the savepoint should hide bindings added after it"
    );
}
