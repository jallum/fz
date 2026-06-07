use super::code::CodeMap;
use super::identity::{FunctionMap, ModuleMap, RootMap};
use super::index::{Compiler2Scheduler, LatestRevision};
use super::namespace::NamespaceStore;

#[derive(Debug)]
pub struct World {
    code: CodeMap,
    modules: ModuleMap,
    functions: FunctionMap,
    roots: RootMap,
    namespaces: NamespaceStore,
    scheduler: Compiler2Scheduler,
}

impl Default for World {
    fn default() -> Self {
        Self {
            code: CodeMap::new(),
            modules: ModuleMap::new(),
            functions: FunctionMap::new(),
            roots: RootMap::new(),
            namespaces: NamespaceStore::new(),
            scheduler: Compiler2Scheduler::new(LatestRevision),
        }
    }
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

    pub fn scheduler(&self) -> &Compiler2Scheduler {
        &self.scheduler
    }

    pub fn scheduler_mut(&mut self) -> &mut Compiler2Scheduler {
        &mut self.scheduler
    }
}
