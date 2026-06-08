use super::{BindingId, CodeMap, FunctionMap, ModuleMap, NamespaceStore, NamespaceSymbol};

#[test]
fn compiler2_namespace_store_shadows_and_restores_by_head() {
    let mut code = CodeMap::new();
    let mut modules = ModuleMap::new();
    let mut functions = FunctionMap::new();
    let mut namespaces = NamespaceStore::new();

    let code_id = code.define(Some("kernel.fz".to_string()), String::new());
    let kernel = modules.reference_named("Kernel");
    let _ = modules.define(kernel, code_id, BindingId::END, Vec::new());
    let dbg_fn = functions.reference(kernel, "dbg", 1);
    let plus_fn = functions.reference(kernel, "+", 2);

    let prelude = namespaces.bind(BindingId::END, "dbg", NamespaceSymbol::Function(dbg_fn));
    namespaces.set_prelude_head(prelude);

    let savepoint = namespaces.prelude_head();
    let head = namespaces.bind(savepoint, "dbg", NamespaceSymbol::Function(plus_fn));
    let head = namespaces.bind(head, "Kernel", NamespaceSymbol::Module(kernel));

    assert_eq!(
        namespaces.lookup(head, "dbg"),
        Some(&NamespaceSymbol::Function(plus_fn)),
        "first match should win within the current head"
    );
    assert_eq!(
        namespaces.lookup(head, "Kernel"),
        Some(&NamespaceSymbol::Module(kernel)),
        "new bindings should resolve immediately"
    );

    let restored = namespaces.restore(savepoint);
    assert_eq!(
        namespaces.lookup(restored, "dbg"),
        Some(&NamespaceSymbol::Function(dbg_fn)),
        "restoring the savepoint should drop shadowing bindings"
    );
    assert_eq!(
        namespaces.lookup(restored, "Kernel"),
        None,
        "restoring the savepoint should hide bindings added after it"
    );
}

#[test]
fn compiler2_namespace_store_reuses_identical_binding_chains() {
    let mut code = CodeMap::new();
    let mut modules = ModuleMap::new();
    let mut functions = FunctionMap::new();
    let mut namespaces = NamespaceStore::new();

    let code_id = code.define(Some("kernel.fz".to_string()), String::new());
    let kernel = modules.reference_named("Kernel");
    let _ = modules.define(kernel, code_id, BindingId::END, Vec::new());
    let dbg_fn = functions.reference(kernel, "dbg", 1);

    let first = namespaces.bind(BindingId::END, "dbg", NamespaceSymbol::Function(dbg_fn));
    let second = namespaces.bind(BindingId::END, "dbg", NamespaceSymbol::Function(dbg_fn));
    assert_eq!(
        first, second,
        "rebinding the same immutable namespace edge should reuse its existing binding id",
    );

    let first_chain = namespaces.bind(first, "Kernel", NamespaceSymbol::Module(kernel));
    let second_chain = namespaces.bind(second, "Kernel", NamespaceSymbol::Module(kernel));
    assert_eq!(
        first_chain, second_chain,
        "replaying the same namespace chain should stabilize on the same head id",
    );
}
