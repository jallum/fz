use super::*;
use crate::diag::Span;
use crate::frontend::protocols::{ImplTarget, InterfaceProtocolImpl};
use crate::modules::identity::{Mfa, ModuleName};
use crate::modules::interface::{InterfaceFn, InterfaceImport, ModuleInterface};

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
        imports: import_facts,
        exports: export_facts,
        types: Vec::new(),
        protocols: Vec::new(),
        protocol_impls: Vec::new(),
        docs: None,
        fingerprint_inputs,
    }
}

#[test]
fn graph_loader_keeps_protocol_impl_callback_namespaces_inside_owner_module() {
    let mut app = interface("App", Vec::new(), vec![("main", 0)]);
    app.protocol_impls.push(InterfaceProtocolImpl {
        protocol: module("Enumerable"),
        target: ImplTarget::module(module("List")),
        callbacks: vec![Mfa::new(module("EnumerableList"), "reduce", 3)],
    });
    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);
    let graph = ModuleGraphLoader::new().load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, []);

    assert!(!graph.interfaces.contains_key(&module("EnumerableList")));
    assert!(!graph.runtime_modules.contains(&module("EnumerableList")));
}

#[test]
fn graph_loader_uses_runtime_interfaces_without_user_storage() {
    let app = interface("App", vec!["Utf8"], vec![("main", 0)]);
    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);

    let graph = ModuleGraphLoader::new().load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, []);

    assert!(graph.interfaces.contains_key(&module("Utf8")));
    assert_eq!(graph.runtime_modules, vec![module("Utf8")]);
    assert!(
        crate::modules::runtime_library::source(&module("Utf8"))
            .expect("runtime source")
            .contains("defmodule Utf8")
    );
}

#[test]
fn graph_loader_follows_runtime_implementation_dependencies() {
    let app = interface("App", vec!["Enum"], vec![("main", 0)]);
    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);

    let graph = ModuleGraphLoader::new().load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, []);

    assert!(graph.interfaces.contains_key(&module("Enum")));
    assert!(graph.interfaces.contains_key(&module("Enumerable")));
    assert!(graph.interfaces.contains_key(&module("List")));
    assert!(graph.interfaces.contains_key(&module("Range")));
    assert!(graph.interfaces.contains_key(&module("Map")));
}

#[test]
fn graph_loader_follows_protocol_impl_protocol_dependency() {
    let mut app = interface("App", Vec::new(), vec![("main", 0)]);
    app.protocol_impls.push(InterfaceProtocolImpl {
        protocol: module("Enumerable"),
        target: ImplTarget::module(module("Range")),
        callbacks: Vec::new(),
    });
    let mut roots = InterfaceTable::new();
    roots.insert(app.name.clone(), app);

    let graph = ModuleGraphLoader::new().load_reachable(&crate::telemetry::ConfiguredTelemetry::new(), &roots, []);

    assert!(graph.interfaces.contains_key(&module("Enumerable")));
}
