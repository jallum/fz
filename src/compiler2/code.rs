#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CodeId(u32);

impl CodeId {
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeRecord {
    name: Option<String>,
    text: String,
}

impl CodeRecord {
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    pub fn text(&self) -> &str {
        &self.text
    }
}

#[derive(Debug, Default)]
pub struct CodeMap {
    slots: Vec<CodeRecord>,
}

impl CodeMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, name: Option<String>, text: String) -> CodeId {
        let id = CodeId(self.slots.len() as u32);
        self.slots.push(CodeRecord { name, text });
        id
    }

    pub fn get(&self, id: CodeId) -> Option<&CodeRecord> {
        self.slots.get(id.0 as usize)
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}
