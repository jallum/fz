//! Compiler2 runtime bootstrap.
//!
//! Compiler2 starts with stable references for runtime modules and imported
//! prelude functions, but it does not eagerly submit runtime source. The first
//! real reference pulls the owning runtime module through ordinary `CodeMap`
//! and source-surface jobs.

use std::collections::HashMap;

use crate::modules::runtime_library;

use super::CodeId;
use super::identity::{ModuleId, ModuleMap};

#[derive(Debug, Clone)]
pub(crate) struct RuntimeModuleCode {
    pub(crate) name: &'static str,
    pub(crate) source: &'static str,
    pub(crate) code_id: Option<CodeId>,
}

pub(crate) fn bootstrap(modules: &mut ModuleMap) -> HashMap<ModuleId, RuntimeModuleCode> {
    let mut runtime_modules = HashMap::new();

    for (name, source) in runtime_library::module_sources() {
        let module = modules.reference_named(name.to_string());
        runtime_modules.insert(
            module,
            RuntimeModuleCode {
                name,
                source,
                code_id: None,
            },
        );
    }

    runtime_modules
}
