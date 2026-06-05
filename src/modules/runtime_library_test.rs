use super::*;
use crate::compiler::Compiler;

fn compiler() -> Compiler {
    Compiler::new()
}

#[test]
fn runtime_library_interfaces_expose_fz_functions_not_primitive_externs() {
    let mut compiler = compiler();
    let interfaces = interface_table(compiler.world_mut(), &NullTelemetry);
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
    let enumerable_artifact = artifact(
        compiler.world_mut(),
        &ModuleName::from_segments(vec!["Enumerable".to_string()]),
        &NullTelemetry,
    )
    .expect("Enumerable artifact")
    .expect("Enumerable runtime module");
    assert!(
        enumerable_artifact
            .fzo
            .unit_payload
            .body
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
        primitive_contract_names(compiler.world_mut(), &NullTelemetry),
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
fn runtime_library_artifacts_round_trip_deterministically() {
    let mut compiler = compiler();
    let artifacts = artifacts(compiler.world_mut(), &NullTelemetry).expect("runtime artifacts");
    assert!(!artifacts.is_empty());

    for artifact in artifacts {
        let fzi_text = artifact.fzi.serialize();
        let fzi = FziArtifact::deserialize(
            &NullTelemetry,
            None,
            &fzi_text,
            Some(&artifact.interface.fingerprint_inputs),
        )
        .expect("fzi roundtrip");
        assert_eq!(fzi.interface.name, artifact.interface.name);
        assert_eq!(fzi.interface.imports, artifact.interface.imports);
        assert_eq!(fzi.interface.types, artifact.interface.types);
        assert_eq!(
            fzi.interface
                .exports
                .iter()
                .map(|f| (&f.name, f.arity, &f.specs))
                .collect::<Vec<_>>(),
            artifact
                .interface
                .exports
                .iter()
                .map(|f| (&f.name, f.arity, &f.specs))
                .collect::<Vec<_>>()
        );

        let fzo_text = artifact.fzo.serialize();
        let fzo = FzoArtifact::deserialize(
            &NullTelemetry,
            None,
            &fzo_text,
            Some(&artifact.fzo.interface_fingerprint),
        )
        .expect("fzo roundtrip");
        assert_eq!(fzo.module, Some(artifact.module));
        assert_eq!(fzo.interface_fingerprint, artifact.interface.fingerprint_inputs);
    }
}

#[test]
fn runtime_library_artifacts_write_load_and_import_like_user_artifacts() {
    let root = temp_dir().join(format!("fz-runtime-artifacts-{}-write-load", std::process::id()));
    let _ = remove_dir_all(&root);
    let store = ArtifactStore::new(&root);
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "module"], capture.handler());
    let mut compiler = compiler();
    let artifacts = artifacts(compiler.world_mut(), &NullTelemetry).expect("runtime artifacts");
    let interfaces = artifacts
        .iter()
        .map(|artifact| (artifact.module.clone(), artifact.interface.clone()))
        .collect::<BTreeMap<_, _>>();

    let fzi_paths = store.write_fzi_artifacts(&tel, &interfaces).expect("write fzi");
    let fzo_paths = store
        .write_fzo_artifacts(&tel, artifacts.iter().map(|artifact| &artifact.fzo))
        .expect("write fzo");
    assert_eq!(fzi_paths.len(), artifacts.len());
    assert_eq!(fzo_paths.len(), artifacts.len());

    let utf8 = ModuleName::from_segments(vec!["Utf8".to_string()]);
    let loaded_interfaces = store.load_interface_table(&tel, [&utf8]).expect("load fzi");
    assert!(
        loaded_interfaces[&utf8]
            .exports
            .iter()
            .any(|export| { export.name == "valid?" && export.arity == 1 && !export.specs.is_empty() })
    );
    let loaded_fzo = store
        .load_fzo_artifact(&tel, &utf8, Some(&loaded_interfaces[&utf8].fingerprint_inputs))
        .expect("load fzo");
    assert_eq!(loaded_fzo.module, Some(utf8));
    assert_eq!(loaded_fzo.unit_payload.format, "fz-runtime-module-v1");

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
        loaded_interfaces,
        &NullTelemetry,
    ) {
        Ok(_) => {}
        Err(_) => panic!("runtime artifact interface resolves like a user artifact"),
    }
    assert!(capture.contains(&["fz", "module", "fzi_written"]));
    assert!(capture.contains(&["fz", "module", "fzo_written"]));
    assert!(capture.contains(&["fz", "module", "fzi_loaded"]));
    assert!(capture.contains(&["fz", "module", "fzo_loaded"]));

    let _ = remove_dir_all(&root);
}

#[test]
fn primitive_prelude_imports_kernel_without_defmodule_body() {
    let mut compiler = compiler();
    let prelude = primitive_prelude_program(compiler.world_mut(), &NullTelemetry);
    assert!(prelude.items.iter().all(|item| !matches!(&**item, Item::Module(_))));
    assert!(
        prelude
            .items
            .iter()
            .any(|item| matches!(&**item, Item::Import { path, .. } if path.dotted() == "Kernel"))
    );
}
