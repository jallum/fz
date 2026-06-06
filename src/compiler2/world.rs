use super::code::CodeMap;
use super::identity::{FunctionMap, ModuleMap, RootMap};
use super::namespace::NamespaceStore;

#[derive(Debug, Default)]
pub struct World {
    code: CodeMap,
    modules: ModuleMap,
    functions: FunctionMap,
    roots: RootMap,
    namespaces: NamespaceStore,
}

impl World {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn code(&self) -> &CodeMap {
        &self.code
    }

    pub fn code_mut(&mut self) -> &mut CodeMap {
        &mut self.code
    }

    pub fn modules(&self) -> &ModuleMap {
        &self.modules
    }

    pub fn modules_mut(&mut self) -> &mut ModuleMap {
        &mut self.modules
    }

    pub fn functions(&self) -> &FunctionMap {
        &self.functions
    }

    pub fn functions_mut(&mut self) -> &mut FunctionMap {
        &mut self.functions
    }

    pub fn roots(&self) -> &RootMap {
        &self.roots
    }

    pub fn roots_mut(&mut self) -> &mut RootMap {
        &mut self.roots
    }

    pub fn namespaces(&self) -> &NamespaceStore {
        &self.namespaces
    }

    pub fn namespaces_mut(&mut self) -> &mut NamespaceStore {
        &mut self.namespaces
    }
}
