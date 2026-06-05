//! Reachable user-provider artifact loading.
//!
//! Runtime-library reachability is compiler-owned (`fz-hua.5`). This loader now
//! only discovers user provider `.fzi` / `.fzo` artifacts that are actually
//! needed for execution.

use crate::compiler::CompilerWorld;
use crate::frontend::resolve::InterfaceTable;
use crate::modules::artifact::FzoArtifact;
use crate::modules::artifact_store::{ArtifactStore, ArtifactStoreError};
use crate::modules::identity::ModuleName;
use crate::modules::interface::ModuleInterface;
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
        compiler: &mut CompilerWorld,
        tel: &dyn Telemetry,
        root_interfaces: &InterfaceTable,
        provider_roots: impl IntoIterator<Item = &'a ModuleName>,
    ) -> Result<ModuleGraph, ArtifactStoreError> {
        let mut queue = VecDeque::new();
        let mut user_modules = BTreeSet::new();
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
            if let Some(existing) = compiler.module_id_for_name(&module)
                && compiler.module(existing).origin != crate::compiler::ModuleOrigin::EmbeddedRuntime
            {
                continue;
            }
            if compiler.discover_runtime_module(&module, tel).is_some() {
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

#[cfg(test)]
#[path = "graph_test.rs"]
mod graph_test;
