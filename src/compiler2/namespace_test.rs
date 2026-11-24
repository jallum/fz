use super::{BindingId, FunctionMap, ModuleMap, NamespaceStore, NamespaceSymbol, TypeName};

#[test]
fn compiler2_namespace_type_binding_coexists_with_a_value_of_the_same_name() {
    let mut modules = ModuleMap::new();
    let mut functions = FunctionMap::new();
    let mut namespaces = NamespaceStore::new();

    let module = modules.reference(crate::modules::identity::ModuleName::parse_dotted("Range").unwrap());
    let type_t = TypeName {
        module,
        name: "t".to_string(),
        arity: 0,
    };
    let value_t = functions.reference(module, None, "t", 0);

    // Reserve the type first (deepest), then bind a value of the same name on
    // top — exactly as `define_scope` does, so values shadow types.
    let with_type = namespaces.bind(BindingId::END, "t", NamespaceSymbol::Type(type_t.clone()));
    let head = namespaces.bind(with_type, "t", NamespaceSymbol::Function(value_t));

    assert_eq!(
        namespaces.lookup(head, "t"),
        Some(&NamespaceSymbol::Function(value_t)),
        "an unfiltered lookup resolves the value, never the shadowed type",
    );
    assert_eq!(
        namespaces.lookup_matching(head, "t", |symbol| matches!(symbol, NamespaceSymbol::Type(_))),
        Some(&NamespaceSymbol::Type(type_t)),
        "a type-position lookup finds the type even when a value of the same name shadows it",
    );
}

#[test]
fn compiler2_namespace_store_shadows_and_restores_by_head() {
    let mut modules = ModuleMap::new();
    let mut functions = FunctionMap::new();
    let mut namespaces = NamespaceStore::new();

    let kernel = modules.reference(crate::modules::identity::ModuleName::parse_dotted("Kernel").unwrap());
    let _ = modules.define(kernel, BindingId::END, crate::compiler2::ModuleInterface::default());
    let dbg_fn = functions.reference(kernel, None, "dbg", 1);
    let plus_fn = functions.reference(kernel, None, "+", 2);

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
    let mut modules = ModuleMap::new();
    let mut functions = FunctionMap::new();
    let mut namespaces = NamespaceStore::new();

    let kernel = modules.reference(crate::modules::identity::ModuleName::parse_dotted("Kernel").unwrap());
    let _ = modules.define(kernel, BindingId::END, crate::compiler2::ModuleInterface::default());
    let dbg_fn = functions.reference(kernel, None, "dbg", 1);

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

#[test]
fn compiler2_namespace_required_macro_is_invisible_to_name_lookup() {
    let mut modules = ModuleMap::new();
    let mut functions = FunctionMap::new();
    let mut namespaces = NamespaceStore::new();

    let module = modules.reference(crate::modules::identity::ModuleName::parse_dotted("Helpers").unwrap());
    let twice = functions.reference(module, None, "twice", 1);
    let other = functions.reference(module, None, "thrice", 1);

    let bound = namespaces.bind(BindingId::END, "twice", NamespaceSymbol::Function(twice));
    let head = namespaces.bind_required_macro(bound, other);

    assert!(
        namespaces.is_required_macro(head, other),
        "a require makes its macro callable by qualified name from there on",
    );
    assert!(
        !namespaces.is_required_macro(bound, other),
        "the scope before the require does not see it",
    );
    assert!(
        !namespaces.is_required_macro(head, twice),
        "a require covers the macro it names, not its neighbours",
    );
    assert_eq!(
        namespaces.lookup(head, "twice"),
        Some(&NamespaceSymbol::Function(twice)),
        "a required macro binds no name, so lookups see the bindings beneath it",
    );
    assert!(
        !namespaces.any_symbol(
            head,
            |symbol| matches!(symbol, NamespaceSymbol::Function(f) if *f == other)
        ),
        "a required macro is not an imported symbol",
    );
}

fn quoted_value(text: &str) -> super::QuotedSourceRoot {
    let telemetry = crate::telemetry::ConfiguredTelemetry::new();
    let mut sources = crate::source::SourceMap::default();
    let version = sources.add_code(Some("value.fz"), text);
    crate::compiler2::parse_quoted_program(&sources, version, &telemetry).expect("quoted parse should succeed")
}

#[test]
fn compiler2_namespace_splice_is_bound_by_what_its_value_says() {
    // A module attribute's value is computed again each time its module is
    // walked, into a new heap. The namespace a definition records must be the
    // same one each time, or the definition never settles.
    let mut namespaces = NamespaceStore::new();
    let first = namespaces.bind(
        BindingId::END,
        "@size",
        NamespaceSymbol::Splice(quoted_value("[1, {:a, 2}]")),
    );
    let rebuilt = namespaces.bind(
        BindingId::END,
        "@size",
        NamespaceSymbol::Splice(quoted_value("[1, {:a, 2}]")),
    );
    let other = namespaces.bind(
        BindingId::END,
        "@size",
        NamespaceSymbol::Splice(quoted_value("[1, {:a, 3}]")),
    );

    assert_eq!(
        first, rebuilt,
        "a splice whose value says the same thing binds the same namespace"
    );
    assert_ne!(
        first, other,
        "a splice whose value differs binds a namespace of its own"
    );
}
