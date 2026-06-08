use super::identity::{FunctionId, ModuleId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct BindingId(u32);

impl BindingId {
    pub const END: Self = Self(0);

    pub fn is_end(self) -> bool {
        self == Self::END
    }
}

pub type Namespace = BindingId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NamespaceSymbol {
    Module(ModuleId),
    Function(FunctionId),
    Macro(FunctionId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Binding {
    name: String,
    symbol: NamespaceSymbol,
    prev: Namespace,
}

#[derive(Debug, Default)]
pub struct NamespaceStore {
    bindings: Vec<Binding>,
    prelude_head: Namespace,
}

impl NamespaceStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bind(&mut self, head: Namespace, name: impl Into<String>, symbol: NamespaceSymbol) -> Namespace {
        let id = BindingId(self.bindings.len() as u32 + 1);
        self.bindings.push(Binding {
            name: name.into(),
            symbol,
            prev: head,
        });
        id
    }

    pub fn lookup(&self, mut head: Namespace, name: &str) -> Option<&NamespaceSymbol> {
        while !head.is_end() {
            let binding = &self.bindings[head.0 as usize - 1];
            if binding.name == name {
                return Some(&binding.symbol);
            }
            head = binding.prev;
        }
        None
    }

    pub fn lookup_matching(
        &self,
        mut head: Namespace,
        name: &str,
        mut predicate: impl FnMut(&NamespaceSymbol) -> bool,
    ) -> Option<&NamespaceSymbol> {
        while !head.is_end() {
            let binding = &self.bindings[head.0 as usize - 1];
            if binding.name == name && predicate(&binding.symbol) {
                return Some(&binding.symbol);
            }
            head = binding.prev;
        }
        None
    }

    pub fn lookup_best_matching<T: Ord>(
        &self,
        mut head: Namespace,
        name: &str,
        mut score: impl FnMut(&NamespaceSymbol) -> Option<T>,
    ) -> Option<&NamespaceSymbol> {
        let mut best = None;
        while !head.is_end() {
            let binding = &self.bindings[head.0 as usize - 1];
            if binding.name == name
                && let Some(candidate) = score(&binding.symbol)
            {
                let replace = best
                    .as_ref()
                    .is_none_or(|(current, _): &(T, &NamespaceSymbol)| candidate > *current);
                if replace {
                    best = Some((candidate, &binding.symbol));
                }
            }
            head = binding.prev;
        }
        best.map(|(_, symbol)| symbol)
    }

    pub fn restore(&self, savepoint: Namespace) -> Namespace {
        savepoint
    }

    pub fn prelude_head(&self) -> Namespace {
        self.prelude_head
    }

    pub fn set_prelude_head(&mut self, head: Namespace) {
        self.prelude_head = head;
    }
}
