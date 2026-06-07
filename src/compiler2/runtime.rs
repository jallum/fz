//! Compiler2 runtime bootstrap.
//!
//! Compiler2 starts with stable references for runtime modules and imported
//! prelude functions, but it does not eagerly submit runtime source. The first
//! real reference pulls the owning runtime module through ordinary `CodeMap`
//! and source-surface jobs.

use std::collections::HashMap;

use crate::ast::Item;
use crate::modules::identity::ModuleName;
use crate::modules::runtime_library;
use crate::telemetry::Telemetry;

use super::CodeId;
use super::identity::{FunctionMap, ModuleId, ModuleMap};
use super::namespace::{NamespaceStore, NamespaceSymbol};

#[derive(Debug, Clone)]
pub(crate) struct RuntimeModuleCode {
    pub(crate) name: &'static str,
    pub(crate) source: &'static str,
    pub(crate) code_id: Option<CodeId>,
    pub(crate) protocol_callbacks: Option<Vec<(String, usize)>>,
}

pub(crate) fn bootstrap(
    tel: &dyn Telemetry,
    modules: &mut ModuleMap,
    functions: &mut FunctionMap,
    namespaces: &mut NamespaceStore,
) -> HashMap<ModuleId, RuntimeModuleCode> {
    let mut prelude = namespaces.prelude_head();
    let mut runtime_modules = HashMap::new();
    let interfaces = runtime_library::interfaces(tel);

    for (name, source) in runtime_library::module_sources() {
        let module = modules.reference_named(name.to_string());
        prelude = namespaces.bind(prelude, name.to_string(), NamespaceSymbol::Module(module));
        let module_name = ModuleName::from_segments(vec![name.to_string()]);
        let protocol_callbacks = interfaces.get(&module_name).and_then(|interface| {
            interface
                .protocols
                .iter()
                .find(|protocol| protocol.name == module_name)
                .map(|protocol| {
                    protocol
                        .callbacks
                        .iter()
                        .map(|callback| (callback.name.clone(), callback.arity))
                        .collect::<Vec<_>>()
                })
        });
        runtime_modules.insert(
            module,
            RuntimeModuleCode {
                name,
                source,
                code_id: None,
                protocol_callbacks,
            },
        );
    }

    for item in runtime_library::primitive_prelude_program(tel).items {
        let Item::Import { path, only, except, .. } = &*item else {
            continue;
        };
        assert!(
            except.is_none(),
            "runtime prelude should use explicit import whitelists"
        );
        let module = modules.reference_named(path.dotted());
        let only = only
            .as_ref()
            .expect("runtime prelude imports should whitelist explicit functions");
        for (name, arity) in only {
            let function = functions.reference(module, name.clone(), *arity);
            prelude = namespaces.bind(prelude, name.clone(), NamespaceSymbol::Function(function));
        }
    }

    namespaces.set_prelude_head(prelude);
    runtime_modules
}
