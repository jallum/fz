use super::identity::{FunctionId, ModuleId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CodeId(u32);

impl CodeId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Code {
    state: CodeState,
    revision: u64,
}

impl Code {
    pub fn state(&self) -> &CodeState {
        &self.state
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodeState {
    Pending,
    Indexed {
        modules: Vec<ModuleId>,
        functions: Vec<FunctionId>,
    },
}

#[derive(Debug, Default)]
pub struct CodeMap {
    slots: Vec<Code>,
    names: Vec<Option<String>>,
    texts: Vec<String>,
}

impl CodeMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, name: Option<String>, text: String) -> CodeId {
        let id = CodeId(self.slots.len() as u32);
        self.slots.push(Code {
            state: CodeState::Pending,
            revision: 0,
        });
        self.names.push(name);
        self.texts.push(text);
        id
    }

    pub fn index(&mut self, id: CodeId, modules: Vec<ModuleId>, functions: Vec<FunctionId>) -> u64 {
        let code = &mut self.slots[id.0 as usize];
        code.state = CodeState::Indexed { modules, functions };
        code.revision += 1;
        code.revision
    }

    pub fn get(&self, id: CodeId) -> Option<&Code> {
        self.slots.get(id.0 as usize)
    }

    pub fn name(&self, id: CodeId) -> Option<&str> {
        self.names.get(id.0 as usize).and_then(|name| name.as_deref())
    }

    pub fn text(&self, id: CodeId) -> Option<&str> {
        self.texts.get(id.0 as usize).map(String::as_str)
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}
