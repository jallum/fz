use std::collections::HashMap;

use crate::ast::FnDef;

use super::code::CodeId;
use super::namespace::NamespaceHead;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ModuleId(u32);

impl ModuleId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FunctionId(u32);

impl FunctionId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RootId(u32);

impl RootId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    state: ModuleState,
    revision: u64,
}

impl Module {
    pub fn state(&self) -> &ModuleState {
        &self.state
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleState {
    Placeholder,
    Defined {
        codes: Vec<CodeId>,
        namespace: NamespaceHead,
    },
}

#[derive(Debug, Clone)]
pub struct Function {
    state: FunctionState,
    revision: u64,
}

impl Function {
    pub fn state(&self) -> &FunctionState {
        &self.state
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }
}

#[derive(Debug, Clone)]
pub enum FunctionState {
    Placeholder,
    Defined { def: FunctionDef },
}

#[derive(Debug, Clone)]
pub struct FunctionDef {
    code: CodeId,
    namespace: NamespaceHead,
    ast: FnDef,
}

impl FunctionDef {
    pub fn new(code: CodeId, namespace: NamespaceHead, ast: FnDef) -> Self {
        Self { code, namespace, ast }
    }

    pub fn code(&self) -> CodeId {
        self.code
    }

    pub fn namespace(&self) -> NamespaceHead {
        self.namespace
    }

    pub fn ast(&self) -> &FnDef {
        &self.ast
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Root {
    state: RootState,
    revision: u64,
}

impl Root {
    pub fn state(&self) -> &RootState {
        &self.state
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RootState {
    Placeholder,
    Defined,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FunctionKey {
    module: Option<ModuleId>,
    name: String,
    arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionRef {
    pub module: Option<ModuleId>,
    pub name: String,
    pub arity: usize,
}

#[derive(Debug, Default)]
pub struct ModuleMap {
    slots: Vec<Module>,
    names: Vec<Option<String>>,
    by_name: HashMap<String, ModuleId>,
}

impl ModuleMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reference_named(&mut self, name: impl Into<String>) -> ModuleId {
        let name = name.into();
        if let Some(id) = self.by_name.get(&name) {
            return *id;
        }
        let id = ModuleId(self.slots.len() as u32);
        self.slots.push(Module {
            state: ModuleState::Placeholder,
            revision: 0,
        });
        self.names.push(Some(name.clone()));
        self.by_name.insert(name, id);
        id
    }

    pub fn define(&mut self, id: ModuleId, code: CodeId, namespace: NamespaceHead) -> u64 {
        let module = &mut self.slots[id.0 as usize];
        let mut codes = match &module.state {
            ModuleState::Placeholder => Vec::new(),
            ModuleState::Defined { codes, .. } => codes.clone(),
        };
        if !codes.contains(&code) {
            codes.push(code);
        }
        module.state = ModuleState::Defined { codes, namespace };
        module.revision += 1;
        module.revision
    }

    pub fn define_anonymous(&mut self, code: CodeId, namespace: NamespaceHead) -> ModuleId {
        let id = ModuleId(self.slots.len() as u32);
        self.slots.push(Module {
            state: ModuleState::Defined {
                codes: vec![code],
                namespace,
            },
            revision: 1,
        });
        self.names.push(None);
        id
    }

    pub fn get(&self, id: ModuleId) -> Option<&Module> {
        self.slots.get(id.0 as usize)
    }

    pub fn name(&self, id: ModuleId) -> Option<&str> {
        self.names.get(id.0 as usize).and_then(|name| name.as_deref())
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}

#[derive(Debug, Default)]
pub struct FunctionMap {
    slots: Vec<Function>,
    refs: Vec<FunctionRef>,
    by_key: HashMap<FunctionKey, FunctionId>,
}

impl FunctionMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reference(&mut self, module: Option<ModuleId>, name: impl Into<String>, arity: usize) -> FunctionId {
        let name = name.into();
        let key = FunctionKey {
            module,
            name: name.clone(),
            arity,
        };
        if let Some(id) = self.by_key.get(&key) {
            return *id;
        }
        let id = FunctionId(self.slots.len() as u32);
        self.slots.push(Function {
            state: FunctionState::Placeholder,
            revision: 0,
        });
        self.refs.push(FunctionRef { module, name, arity });
        self.by_key.insert(key, id);
        id
    }

    pub fn define(&mut self, id: FunctionId, def: FunctionDef) -> u64 {
        let function = &mut self.slots[id.0 as usize];
        function.state = FunctionState::Defined { def };
        function.revision += 1;
        function.revision
    }

    pub fn get(&self, id: FunctionId) -> Option<&Function> {
        self.slots.get(id.0 as usize)
    }

    pub fn reference_for(&self, id: FunctionId) -> Option<&FunctionRef> {
        self.refs.get(id.0 as usize)
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}

#[derive(Debug, Default)]
pub struct RootMap {
    slots: Vec<Root>,
    names: Vec<Option<String>>,
    by_name: HashMap<String, RootId>,
}

impl RootMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn reference_named(&mut self, name: impl Into<String>) -> RootId {
        let name = name.into();
        if let Some(id) = self.by_name.get(&name) {
            return *id;
        }
        let id = RootId(self.slots.len() as u32);
        self.slots.push(Root {
            state: RootState::Placeholder,
            revision: 0,
        });
        self.names.push(Some(name.clone()));
        self.by_name.insert(name, id);
        id
    }

    pub fn define_named(&mut self, name: impl Into<String>) -> RootId {
        let id = self.reference_named(name);
        let root = &mut self.slots[id.0 as usize];
        root.state = RootState::Defined;
        root.revision += 1;
        id
    }

    pub fn define_anonymous(&mut self) -> RootId {
        let id = RootId(self.slots.len() as u32);
        self.slots.push(Root {
            state: RootState::Defined,
            revision: 1,
        });
        self.names.push(None);
        id
    }

    pub fn get(&self, id: RootId) -> Option<&Root> {
        self.slots.get(id.0 as usize)
    }

    pub fn name(&self, id: RootId) -> Option<&str> {
        self.names.get(id.0 as usize).and_then(|name| name.as_deref())
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}
