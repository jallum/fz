use super::identity::{FunctionId, ModuleId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BindingId(u32);

pub type NamespaceHead = Option<BindingId>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NamespaceSymbol {
    Module(ModuleId),
    Functions(Vec<FunctionId>),
    Macros(Vec<FunctionId>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Binding {
    name: String,
    symbol: NamespaceSymbol,
    prev: NamespaceHead,
}

#[derive(Debug, Default)]
pub struct NamespaceStore {
    bindings: Vec<Binding>,
    prelude_head: NamespaceHead,
}

impl NamespaceStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bind(&mut self, head: NamespaceHead, name: impl Into<String>, symbol: NamespaceSymbol) -> NamespaceHead {
        let id = BindingId(self.bindings.len() as u32);
        self.bindings.push(Binding {
            name: name.into(),
            symbol,
            prev: head,
        });
        Some(id)
    }

    pub fn lookup(&self, mut head: NamespaceHead, name: &str) -> Option<&NamespaceSymbol> {
        while let Some(binding_id) = head {
            let binding = &self.bindings[binding_id.0 as usize];
            if binding.name == name {
                return Some(&binding.symbol);
            }
            head = binding.prev;
        }
        None
    }

    pub fn restore(&self, savepoint: NamespaceHead) -> NamespaceHead {
        savepoint
    }

    pub fn prelude_head(&self) -> NamespaceHead {
        self.prelude_head
    }

    pub fn set_prelude_head(&mut self, head: NamespaceHead) {
        self.prelude_head = head;
    }
}
