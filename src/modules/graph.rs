//! Reachable runtime-library module loading.
//!
//! The graph loader owns the policy for moving from root interfaces to the
//! runtime-library modules a runnable image needs.

use crate::frontend::resolve::InterfaceTable;
use crate::modules::identity::ModuleName;
use crate::modules::interface::ModuleInterface;
use crate::modules::runtime_library;
use crate::telemetry::Telemetry;
use std::collections::{BTreeSet, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGraph {
    pub interfaces: InterfaceTable,
    pub runtime_modules: Vec<ModuleName>,
}

#[derive(Debug, Clone, Default)]
pub struct ModuleGraphLoader;

impl ModuleGraphLoader {
    pub fn new() -> Self {
        Self
    }

    pub fn load_reachable<'a>(
        &self,
        tel: &dyn Telemetry,
        root_interfaces: &InterfaceTable,
        runtime_roots: impl IntoIterator<Item = &'a ModuleName>,
    ) -> ModuleGraph {
        let mut queue = VecDeque::new();
        let mut runtime_modules = BTreeSet::new();
        let mut interfaces = root_interfaces.clone();

        for interface in root_interfaces.values() {
            enqueue_imports(&mut queue, interface);
            enqueue_protocol_impl_protocols(&mut queue, interface);
        }
        for module in runtime_roots {
            queue.push_back(module.clone());
        }

        while let Some(module) = queue.pop_front() {
            if interfaces.contains_key(&module) {
                continue;
            }
            let Some(interface) = runtime_library::interface(&module, tel) else {
                continue;
            };
            interfaces.insert(module, interface.clone());
            enqueue_imports(&mut queue, &interface);
            enqueue_protocol_impl_protocols(&mut queue, &interface);
            enqueue_runtime_implementation_imports(&mut queue, &interface, tel);
            enqueue_runtime_protocol_impls(&mut queue, &interfaces, &interface, tel);
            runtime_modules.insert(interface.name.clone());
        }

        ModuleGraph {
            interfaces,
            runtime_modules: runtime_modules.into_iter().collect(),
        }
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
