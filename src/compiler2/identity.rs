use std::collections::HashMap;

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
}

impl Module {
    pub fn state(&self) -> &ModuleState {
        &self.state
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleState {
    Placeholder,
    Defined,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    state: FunctionState,
}

impl Function {
    pub fn state(&self) -> &FunctionState {
        &self.state
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionState {
    Placeholder,
    Defined,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Root {
    state: RootState,
}

impl Root {
    pub fn state(&self) -> &RootState {
        &self.state
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RootState {
    Placeholder,
    Defined,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct FunctionKey {
    module: ModuleId,
    name: String,
    arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionRef {
    pub module: ModuleId,
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
        });
        self.names.push(Some(name.clone()));
        self.by_name.insert(name, id);
        id
    }

    pub fn define_named(&mut self, name: impl Into<String>) -> ModuleId {
        let id = self.reference_named(name);
        self.slots[id.0 as usize].state = ModuleState::Defined;
        id
    }

    pub fn define_anonymous(&mut self) -> ModuleId {
        let id = ModuleId(self.slots.len() as u32);
        self.slots.push(Module {
            state: ModuleState::Defined,
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

    pub fn reference(&mut self, module: ModuleId, name: impl Into<String>, arity: usize) -> FunctionId {
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
        });
        self.refs.push(FunctionRef { module, name, arity });
        self.by_key.insert(key, id);
        id
    }

    pub fn define(&mut self, module: ModuleId, name: impl Into<String>, arity: usize) -> FunctionId {
        let id = self.reference(module, name, arity);
        self.slots[id.0 as usize].state = FunctionState::Defined;
        id
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
        });
        self.names.push(Some(name.clone()));
        self.by_name.insert(name, id);
        id
    }

    pub fn define_named(&mut self, name: impl Into<String>) -> RootId {
        let id = self.reference_named(name);
        self.slots[id.0 as usize].state = RootState::Defined;
        id
    }

    pub fn define_anonymous(&mut self) -> RootId {
        let id = RootId(self.slots.len() as u32);
        self.slots.push(Root {
            state: RootState::Defined,
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
