//! Reachable module artifact loading.
//!
//! The graph loader owns the policy for moving from root interfaces to the
//! provider `.fzi`/`.fzo` artifacts actually needed to link a runnable image.

use crate::module_artifact::FzoArtifact;
use crate::module_artifact_store::{ArtifactStore, ArtifactStoreError};
use crate::module_identity::ModuleName;
use crate::module_interface::ModuleInterface;
use crate::resolve::InterfaceTable;
use std::collections::{BTreeSet, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGraph {
    pub interfaces: InterfaceTable,
    pub objects: Vec<FzoArtifact>,
}

#[derive(Debug, Clone)]
pub struct ModuleGraphLoader {
    store: ArtifactStore,
    runtime_interfaces: InterfaceTable,
}

impl ModuleGraphLoader {
    pub fn new(store: ArtifactStore) -> Self {
        Self {
            store,
            runtime_interfaces: crate::runtime_library::interface_table(),
        }
    }

    pub fn load_reachable<'a>(
        &self,
        root_interfaces: &InterfaceTable,
        provider_roots: impl IntoIterator<Item = &'a ModuleName>,
    ) -> Result<ModuleGraph, ArtifactStoreError> {
        let mut queue = VecDeque::new();
        let mut user_modules = BTreeSet::new();
        let mut interfaces = root_interfaces.clone();

        for interface in root_interfaces.values() {
            enqueue_imports(&mut queue, interface);
        }
        for module in provider_roots {
            queue.push_back(module.clone());
        }

        while let Some(module) = queue.pop_front() {
            if interfaces.contains_key(&module) {
                continue;
            }
            if let Some(interface) = self.runtime_interfaces.get(&module) {
                interfaces.insert(module, interface.clone());
                enqueue_imports(&mut queue, interface);
                continue;
            }

            let artifact = self.store.load_fzi_artifact(&module, None)?;
            let interface = artifact.interface;
            enqueue_imports(&mut queue, &interface);
            user_modules.insert(interface.name.clone());
            interfaces.insert(interface.name.clone(), interface);
        }

        let mut objects = Vec::new();
        for module in user_modules {
            let expected = interfaces
                .get(&module)
                .map(|interface| interface.fingerprint_inputs.as_slice());
            objects.push(self.store.load_fzo_artifact(&module, expected)?);
        }

        Ok(ModuleGraph {
            interfaces,
            objects,
        })
    }
}

fn enqueue_imports(queue: &mut VecDeque<ModuleName>, interface: &ModuleInterface) {
    for import in &interface.imports {
        queue.push_back(import.module.clone());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::Span;
    use crate::module_artifact::FzoArtifact;
    use crate::module_artifact_store::ArtifactStore;
    use crate::module_identity::ModuleName;
    use crate::module_interface::{
        FZ_INTERFACE_ABI_VERSION, InterfaceFn, InterfaceImport, ModuleInterface,
    };

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
                spec: None,
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
            docs: None,
            fingerprint_inputs,
        }
    }

    fn fzo(interface: &ModuleInterface, source: &str) -> FzoArtifact {
        let unit = crate::ir_codegen::CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface.clone()),
            crate::diag::Diagnostics::new(),
        );
        let runtime = crate::ir_codegen::RuntimeUnitMetadata::from_ir_module(
            Some(interface.name.clone()),
            &unit.code,
        );
        FzoArtifact::from_unit_source(&unit, &runtime, source, Vec::new())
    }

    #[test]
    fn graph_loader_loads_only_reachable_user_artifacts() {
        let root =
            std::env::temp_dir().join(format!("fz-module-graph-{}-reachable", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        let store = ArtifactStore::new(&root);

        let app = interface("App", vec!["Math"], vec![("main", 0)]);
        let math = interface("Math", Vec::new(), vec![("add", 2)]);
        let extra = interface("Extra", Vec::new(), vec![("unused", 0)]);
        let mut artifacts = InterfaceTable::new();
        artifacts.insert(math.name.clone(), math.clone());
        artifacts.insert(extra.name.clone(), extra.clone());
        store.write_fzi_artifacts(&artifacts).unwrap();
        store
            .write_fzo_artifacts([&fzo(
                &math,
                "defmodule Math do\n  fn add(x, y), do: x + y\nend\n",
            )])
            .unwrap();
        let extra_path = store.object_path(&extra.name).unwrap();
        if let Some(parent) = extra_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&extra_path, "not a valid fzo").unwrap();

        let mut roots = InterfaceTable::new();
        roots.insert(app.name.clone(), app);
        let graph = ModuleGraphLoader::new(store)
            .load_reachable(&roots, [])
            .expect("load graph");

        assert!(graph.interfaces.contains_key(&module("App")));
        assert!(graph.interfaces.contains_key(&module("Math")));
        assert!(!graph.interfaces.contains_key(&module("Extra")));
        assert_eq!(graph.objects.len(), 1);
        assert_eq!(graph.objects[0].module, Some(module("Math")));

        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn graph_loader_rejects_fzo_interface_fingerprint_mismatch() {
        let root = std::env::temp_dir().join(format!(
            "fz-module-graph-{}-fingerprint",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        let store = ArtifactStore::new(&root);

        let app = interface("App", vec!["Math"], vec![("main", 0)]);
        let math_fzi = interface("Math", Vec::new(), vec![("add", 2)]);
        let math_fzo = interface("Math", Vec::new(), vec![("sub", 2)]);
        let mut artifacts = InterfaceTable::new();
        artifacts.insert(math_fzi.name.clone(), math_fzi.clone());
        store.write_fzi_artifacts(&artifacts).unwrap();
        store
            .write_fzo_artifacts([&fzo(
                &math_fzo,
                "defmodule Math do\n  fn sub(x, y), do: x - y\nend\n",
            )])
            .unwrap();

        let mut roots = InterfaceTable::new();
        roots.insert(app.name.clone(), app);
        let err = ModuleGraphLoader::new(store)
            .load_reachable(&roots, [])
            .unwrap_err();

        assert!(err.to_string().contains("fingerprint"));

        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn graph_loader_uses_runtime_interfaces_without_user_artifacts() {
        let store = ArtifactStore::new(
            std::env::temp_dir().join(format!("fz-module-graph-{}-runtime", std::process::id())),
        );
        let app = interface("App", vec!["Utf8"], vec![("main", 0)]);
        let mut roots = InterfaceTable::new();
        roots.insert(app.name.clone(), app);

        let graph = ModuleGraphLoader::new(store)
            .load_reachable(&roots, [])
            .expect("load graph");

        assert!(graph.interfaces.contains_key(&module("Utf8")));
        assert!(graph.objects.is_empty());
    }
}
