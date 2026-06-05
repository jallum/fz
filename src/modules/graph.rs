//! Reachable module artifact loading.
//!
//! The graph loader owns the policy for moving from root interfaces to the
//! provider `.fzi`/`.fzo` artifacts actually needed to link a runnable image.

use crate::frontend::resolve::InterfaceTable;
use crate::modules::artifact::FzoArtifact;
use crate::modules::artifact_store::{ArtifactStore, ArtifactStoreError};
use crate::modules::identity::ModuleName;
use crate::modules::interface::ModuleInterface;
use crate::modules::runtime_library;
use crate::telemetry::Telemetry;
use std::collections::{BTreeSet, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGraph {
    pub interfaces: InterfaceTable,
    pub objects: Vec<FzoArtifact>,
}

#[derive(Debug, Clone)]
pub struct ModuleGraphLoader {
    store: ArtifactStore,
}

impl ModuleGraphLoader {
    pub fn new(store: ArtifactStore) -> Self {
        Self { store }
    }

    pub fn load_reachable<'a>(
        &self,
        tel: &dyn Telemetry,
        root_interfaces: &InterfaceTable,
        provider_roots: impl IntoIterator<Item = &'a ModuleName>,
    ) -> Result<ModuleGraph, ArtifactStoreError> {
        let mut queue = VecDeque::new();
        let mut user_modules = BTreeSet::new();
        let mut runtime_modules = BTreeSet::new();
        let mut interfaces = root_interfaces.clone();

        for interface in root_interfaces.values() {
            enqueue_imports(&mut queue, interface);
            enqueue_protocol_impl_protocols(&mut queue, interface);
        }
        for module in provider_roots {
            queue.push_back(module.clone());
        }

        while let Some(module) = queue.pop_front() {
            if interfaces.contains_key(&module) {
                continue;
            }
            if let Some(interface) = runtime_library::interface(&module, tel) {
                interfaces.insert(module, interface.clone());
                enqueue_imports(&mut queue, &interface);
                enqueue_protocol_impl_protocols(&mut queue, &interface);
                enqueue_runtime_implementation_imports(&mut queue, &interface, tel);
                enqueue_runtime_protocol_impls(&mut queue, &interfaces, &interface, tel);
                runtime_modules.insert(interface.name.clone());
                continue;
            }

            let artifact = self.store.load_fzi_artifact(tel, &module, None)?;
            let interface = artifact.interface;
            enqueue_imports(&mut queue, &interface);
            enqueue_protocol_impl_protocols(&mut queue, &interface);
            user_modules.insert(interface.name.clone());
            interfaces.insert(interface.name.clone(), interface);
        }

        let mut objects = Vec::new();
        for module in runtime_modules {
            let Some(artifact) = runtime_library::artifact(&module, tel) else {
                continue;
            };
            objects.push(artifact.fzo);
        }
        for module in user_modules {
            let expected = interfaces
                .get(&module)
                .map(|interface| interface.fingerprint_inputs.as_slice());
            objects.push(self.store.load_fzo_artifact(tel, &module, expected)?);
        }

        Ok(ModuleGraph { interfaces, objects })
    }
}

fn enqueue_imports(queue: &mut VecDeque<ModuleName>, interface: &ModuleInterface) {
    for import in &interface.imports {
        queue.push_back(import.module.clone());
    }
}

fn enqueue_protocol_impl_protocols(queue: &mut VecDeque<ModuleName>, interface: &ModuleInterface) {
    let local_protocols = interface
        .protocols
        .iter()
        .map(|protocol| &protocol.name)
        .collect::<BTreeSet<_>>();
    for protocol_impl in &interface.protocol_impls {
        if !local_protocols.contains(&protocol_impl.protocol) {
            queue.push_back(protocol_impl.protocol.clone());
        }
    }
}

fn enqueue_runtime_implementation_imports(
    queue: &mut VecDeque<ModuleName>,
    interface: &ModuleInterface,
    tel: &dyn Telemetry,
) {
    for module in runtime_library::implementation_dependencies(&interface.name, tel) {
        queue.push_back(module);
    }
}

fn enqueue_runtime_protocol_impls(
    queue: &mut VecDeque<ModuleName>,
    loaded: &InterfaceTable,
    interface: &ModuleInterface,
    tel: &dyn Telemetry,
) {
    if interface.protocols.is_empty() {
        return;
    }
    let protocols = interface
        .protocols
        .iter()
        .map(|protocol| protocol.name.clone())
        .collect::<Vec<_>>();
    for (module, candidate) in runtime_library::interfaces(tel) {
        if loaded.contains_key(&module) {
            continue;
        }
        if candidate
            .protocol_impls
            .iter()
            .any(|protocol_impl| protocols.contains(&protocol_impl.protocol))
        {
            queue.push_back(module);
        }
    }
}

#[cfg(test)]
#[path = "graph_test.rs"]
mod graph_test;
