use super::*;
use crate::diag::{Diagnostics, Span};
use crate::frontend::protocols::{ImplTarget, InterfaceProtocolImpl};
use crate::fz_ir::Module;
use crate::ir_codegen::CompiledUnit;
use crate::modules::artifact::FzoArtifact;
use crate::modules::artifact_store::ArtifactStore;
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{FZ_INTERFACE_ABI_VERSION, InterfaceFn, InterfaceImport, ModuleInterface};

fn module(name: &str) -> ModuleName {
    ModuleName::from_segments(vec![name.to_string()])
}

fn interface(name: &str, imports: Vec<&str>, exports: Vec<(&str, usize)>) -> ModuleInterface {
    let module_name = module(name);
    let import_facts = imports
        .into_iter()
        .map(|name| InterfaceImport {
            module: module(name),
            only: Vec::new(),
            except: Vec::new(),
        })
        .collect::<Vec<_>>();
    let export_facts = exports
        .into_iter()
        .map(|(name, arity)| InterfaceFn {
            name: name.to_string(),
            arity,
            specs: Vec::new(),
            name_span: Span::DUMMY,
        })
        .collect::<Vec<_>>();
    let fingerprint_inputs = export_facts
        .iter()
        .map(|export| format!("export:{module_name}.{}:{}", export.name, export.arity))
        .collect();
    ModuleInterface {
        name: module_name,
        abi_version: FZ_INTERFACE_ABI_VERSION,
        imports: import_facts,
        exports: export_facts,
        types: Vec::new(),
        protocols: Vec::new(),
        protocol_impls: Vec::new(),
        docs: None,
        fingerprint_inputs,
    }
}

fn fzo(interface: &ModuleInterface, source: &str) -> FzoArtifact {
    let unit = CompiledUnit::from_ir_module(Module::new(), Some(interface.clone()), Diagnostics::new());
    FzoArtifact::from_unit_source(&unit, source, Vec::new())
}

#[test]
fn graph_loader_loads_only_reachable_user_artifacts() {
    let root = std::env::temp_dir().join(format!("fz-module-graph-{}-reachable", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let store = ArtifactStore::new(&root);

    let app = interface("App", vec!["Math"], vec![("main", 0)]);
    let math = interface("Math", Vec::new(), vec![("add", 2)]);
    let extra = interface("Extra", Vec::new(), vec![("unused", 0)]);
    let mut artifacts = InterfaceTable::new();
    artifacts.insert(math.name.clone(), math.clone());
    artifacts.insert(extra.name.clone(), extra.clone());
    store
        .write_fzi_artifacts(&crate::telemetry::ConfiguredTelemetry::new(), &artifacts)
        .unwrap();
    store
        .write_fzo_artifacts(
            &crate::telemetry::ConfiguredTelemetry::new(),
            [&fzo(&math, "defmodule Math do\n  fn add(x, y), do: x + y\nend\n")],
        )
        .unwrap();
    let extra_path = store.object_path(&extra.name).unwrap();
    if let Some(parent) = extra_path.parent() {
        std::fs::create_dir_all(parent).unwrap();
    }
    std::fs::write(&extra_path, "not a valid fzo").unwrap();

    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);
    let graph = ModuleGraphLoader::new(store)
        .load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, [])
        .expect("load graph");

    assert!(graph.interfaces.contains_key(&module("App")));
    assert!(graph.interfaces.contains_key(&module("Math")));
    assert!(!graph.interfaces.contains_key(&module("Extra")));
    assert_eq!(graph.objects.len(), 1);
    assert_eq!(graph.objects[0].module, Some(module("Math")));

    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn graph_loader_keeps_protocol_impl_callback_namespaces_inside_owner_artifact() {
    let root = std::env::temp_dir().join(format!("fz-module-graph-{}-protocol-impl", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let store = ArtifactStore::new(&root);

    let mut app = interface("App", Vec::new(), vec![("main", 0)]);
    app.protocol_impls.push(InterfaceProtocolImpl {
        protocol: module("Enumerable"),
        target: ImplTarget::module(module("List")),
        callbacks: vec![ExportKey::new(module("EnumerableList"), "reduce", 3)],
    });
    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);
    let graph = ModuleGraphLoader::new(store)
        .load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, [])
        .expect("load graph");

    assert!(!graph.interfaces.contains_key(&module("EnumerableList")));
    assert!(
        !graph
            .objects
            .iter()
            .any(|object| object.module == Some(module("EnumerableList"))),
        "callback namespace must not be loaded as its own object"
    );

    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn graph_loader_rejects_fzo_interface_fingerprint_mismatch() {
    let root = std::env::temp_dir().join(format!("fz-module-graph-{}-fingerprint", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    let store = ArtifactStore::new(&root);

    let app = interface("App", vec!["Math"], vec![("main", 0)]);
    let math_fzi = interface("Math", Vec::new(), vec![("add", 2)]);
    let math_fzo = interface("Math", Vec::new(), vec![("sub", 2)]);
    let mut artifacts = InterfaceTable::new();
    artifacts.insert(math_fzi.name.clone(), math_fzi.clone());
    store
        .write_fzi_artifacts(&crate::telemetry::ConfiguredTelemetry::new(), &artifacts)
        .unwrap();
    store
        .write_fzo_artifacts(
            &crate::telemetry::ConfiguredTelemetry::new(),
            [&fzo(&math_fzo, "defmodule Math do\n  fn sub(x, y), do: x - y\nend\n")],
        )
        .unwrap();

    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);
    let err = ModuleGraphLoader::new(store)
        .load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, [])
        .unwrap_err();

    assert!(err.to_string().contains("fingerprint"));

    let _ = std::fs::remove_dir_all(&root);
}

#[test]
fn graph_loader_uses_runtime_interfaces_without_user_artifacts() {
    let store =
        ArtifactStore::new(std::env::temp_dir().join(format!("fz-module-graph-{}-runtime", std::process::id())));
    let app = interface("App", vec!["Utf8"], vec![("main", 0)]);
    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);

    let graph = ModuleGraphLoader::new(store)
        .load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, [])
        .expect("load graph");

    assert!(graph.interfaces.contains_key(&module("Utf8")));
    assert_eq!(graph.objects.len(), 1);
    assert_eq!(graph.objects[0].module, Some(module("Utf8")));
    assert_eq!(graph.objects[0].unit_payload.format, "fz-runtime-module-v1");
    assert!(
        graph.objects[0]
            .source_unit_text(&crate::telemetry::ConfiguredTelemetry::new())
            .expect("runtime fzo source")
            .contains("defmodule Utf8")
    );
}

#[test]
fn graph_loader_follows_runtime_implementation_dependencies() {
    let store = ArtifactStore::new(
        std::env::temp_dir().join(format!("fz-module-graph-{}-runtime-impl-deps", std::process::id())),
    );
    let app = interface("App", vec!["Enum"], vec![("main", 0)]);
    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);

    let graph = ModuleGraphLoader::new(store)
        .load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, [])
        .expect("load graph");

    assert!(graph.interfaces.contains_key(&module("Enum")));
    assert!(graph.interfaces.contains_key(&module("Enumerable")));
    assert!(graph.interfaces.contains_key(&module("List")));
    assert!(graph.interfaces.contains_key(&module("Range")));
    assert!(graph.interfaces.contains_key(&module("Map")));
}

#[test]
fn graph_loader_follows_protocol_impl_protocol_dependency() {
    let store = ArtifactStore::new(
        std::env::temp_dir().join(format!("fz-module-graph-{}-protocol-impl-protocol", std::process::id())),
    );
    let mut app = interface("App", Vec::new(), vec![("main", 0)]);
    app.protocol_impls.push(InterfaceProtocolImpl {
        protocol: module("Enumerable"),
        target: ImplTarget::module(module("Range")),
        callbacks: Vec::new(),
    });
    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);

    let graph = ModuleGraphLoader::new(store)
        .load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, [])
        .expect("load graph");

    assert!(graph.interfaces.contains_key(&module("Enumerable")));
}
