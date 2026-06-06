use super::*;

#[test]
fn runtime_library_interfaces_expose_fz_functions_not_primitive_externs() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let interfaces = interface_table(&tel);
    let utf8 = interfaces
        .get(&ModuleName::from_segments(vec!["Utf8".to_string()]))
        .expect("Utf8 interface");

    let exports = utf8
        .exports
        .iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect::<Vec<_>>();
    assert_eq!(exports, vec!["from_bytes/1", "from_bytes!/1", "to_bytes/1", "valid?/1"]);
    assert!(!exports.iter().any(|name| name.starts_with("fz_")));

    let enumerable = interfaces
        .get(&ModuleName::from_segments(vec!["Enumerable".to_string()]))
        .expect("Enumerable interface");
    assert!(
        enumerable
            .protocols
            .iter()
            .any(|protocol| protocol.name.dotted() == "Enumerable")
    );
    assert!(enumerable.exports.is_empty());
    let list_module = interfaces
        .get(&ModuleName::from_segments(vec!["List".to_string()]))
        .expect("List interface");
    let range_module = interfaces
        .get(&ModuleName::from_segments(vec!["Range".to_string()]))
        .expect("Range interface");
    let map_module = interfaces
        .get(&ModuleName::from_segments(vec!["Map".to_string()]))
        .expect("Map interface");

    assert!(list_module.protocol_impls.iter().any(|protocol_impl| {
        protocol_impl.protocol.dotted() == "Enumerable"
            && protocol_impl.target.display_name() == "List"
            && protocol_impl
                .callbacks
                .iter()
                .any(|callback| callback.module.dotted() == "Enumerable.List")
    }));
    assert!(range_module.protocol_impls.iter().any(|protocol_impl| {
        protocol_impl.protocol.dotted() == "Enumerable"
            && protocol_impl.target.display_name() == "Range"
            && protocol_impl
                .callbacks
                .iter()
                .any(|callback| callback.module.dotted() == "Enumerable.Range")
    }));
    assert!(map_module.protocol_impls.iter().any(|protocol_impl| {
        protocol_impl.protocol.dotted() == "Enumerable"
            && protocol_impl.target.display_name() == "Map"
            && protocol_impl
                .callbacks
                .iter()
                .any(|callback| callback.module.dotted() == "Enumerable.Map")
    }));
    assert!(
        !interfaces
            .keys()
            .any(|module| module.dotted() == "Enumerable.Enumerable")
    );
    assert!(
        source(&ModuleName::from_segments(vec!["Enumerable".to_string()]))
            .expect("Enumerable source")
            .trim_start()
            .starts_with("defprotocol Enumerable")
    );

    let enum_module = interfaces
        .get(&ModuleName::from_segments(vec!["Enum".to_string()]))
        .expect("Enum interface");
    let enum_exports = enum_module
        .exports
        .iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect::<Vec<_>>();
    for export in ["count/1", "member?/2", "reduce/3", "slice/1", "sort/1", "sort/2"] {
        assert!(enum_exports.contains(&export.to_string()));
    }

    let kernel = interfaces
        .get(&ModuleName::from_segments(vec!["Kernel".to_string()]))
        .expect("Kernel interface");
    let kernel_exports = kernel
        .exports
        .iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect::<Vec<_>>();
    for export in ["+/2", "-/2", "*/2", "//2", "%/2"] {
        assert!(
            kernel_exports.contains(&export.to_string()),
            "Kernel should export arithmetic operator {export}; exports: {kernel_exports:?}"
        );
    }

    let list_exports = list_module
        .exports
        .iter()
        .map(|f| format!("{}/{}", f.name, f.arity))
        .collect::<Vec<_>>();
    assert_eq!(
        list_exports,
        vec![
            "concat/2",
            "count/1",
            "member?/2",
            "reduce/3",
            "reverse/2",
            "subtract/2"
        ]
    );

    assert_eq!(
        utf8.docs.as_deref(),
        Some("UTF-8 validation and branding for byte-aligned binaries.")
    );
    let specs = utf8
        .exports
        .iter()
        .map(|export| {
            let spec = export.specs.first().expect("runtime export spec");
            (
                format!("{}/{}", export.name, export.arity),
                spec.params.clone(),
                spec.result.clone(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        specs,
        vec![
            (
                "from_bytes/1".to_string(),
                vec!["Ident(\"binary\")".to_string()],
                "LBrace Atom(\"ok\") Comma Ident(\"utf8\") RBrace Bar LBrace Atom(\"error\") Comma Atom(\"invalid_utf8\") RBrace".to_string(),
            ),
            (
                "from_bytes!/1".to_string(),
                vec!["Ident(\"binary\")".to_string()],
                "Ident(\"utf8\")".to_string(),
            ),
            (
                "to_bytes/1".to_string(),
                vec!["Ident(\"utf8\")".to_string()],
                "Ident(\"binary\")".to_string(),
            ),
            (
                "valid?/1".to_string(),
                vec!["Ident(\"binary\")".to_string()],
                "Ident(\"bool\")".to_string(),
            ),
        ]
    );

    assert_eq!(
        primitive_contract_names(&tel),
        vec![
            "fz_binary_concat/2",
            "fz_bitstring_valid_utf8/1",
            "fz_brand_bitstring_as_utf8/1",
            "fz_dbg_value/1",
            "fz_make_ref/0",
            "fz_make_resource/2",
            "fz_map_count/1",
            "fz_map_entry_key/2",
            "fz_map_entry_value/2",
            "fz_panic/1",
            "fz_process_heap_alloc_stats/0",
            "fz_self/0",
            "fz_send/2",
            "fz_spawn/1",
            "fz_spawn_opt/2",
        ]
    );
}

#[test]
fn runtime_library_sources_resolve_like_user_interfaces() {
    let mut t = crate::types::new();
    let consumer = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  @spec accepts(any) :: bool
  fn accepts(bytes), do: valid?(bytes)
end
"#;
    match compile_source_with_interface_table(
        &mut t,
        consumer.to_string(),
        "consumer.fz".to_string(),
        interface_table(&crate::telemetry::ConfiguredTelemetry::new()),
        &crate::telemetry::ConfiguredTelemetry::new(),
    ) {
        Ok(_) => {}
        Err(_) => panic!("runtime interfaces resolve like user module interfaces"),
    }
}

#[test]
fn primitive_prelude_imports_kernel_without_defmodule_body() {
    let prelude = primitive_prelude_program(&crate::telemetry::ConfiguredTelemetry::new());
    assert!(prelude.items.iter().all(|item| !matches!(&**item, Item::Module(_))));
    assert!(
        prelude
            .items
            .iter()
            .any(|item| matches!(&**item, Item::Import { path, .. } if path.dotted() == "Kernel"))
    );
}
