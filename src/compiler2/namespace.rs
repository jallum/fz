use super::identity::{FunctionId, ModuleId, TypeName};
use super::source::{Horizon, QuotedSourceRoot};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct BindingId(u32);

impl BindingId {
    pub const END: Self = Self(0);

    pub fn is_end(self) -> bool {
        self == Self::END
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }
}

pub type Namespace = BindingId;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NamespaceSymbol {
    Module(ModuleId),
    Function(FunctionId),
    Macro(FunctionId),
    Callable(FunctionId),
    /// A type-position name bound to its identity. Resolution (fz-rh2.12.3)
    /// reads it; value/callable lookups filter it out, so a type and a value
    /// of the same name never collide.
    Type(TypeName),
    /// A name bound to a quoted AST snippet, spliced in place when the name is
    /// referenced during macro expansion. The mechanism is generic: `__ENV__`
    /// and `__MODULE__` are bound this way just before a body is expanded.
    Splice(QuotedSourceRoot),
}

/// What one link of a scope's binding chain says.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Entry {
    /// A name bound to a symbol; every name lookup reads these. `imported_from`
    /// names the module an `import` took the binding from.
    Named {
        name: String,
        symbol: NamespaceSymbol,
        imported_from: Option<ModuleId>,
    },
    /// Every binding an earlier `import` of this module made is gone from
    /// here back: importing a module again replaces what the first import
    /// brought in.
    ImportsReplaced(ModuleId),
    /// A macro `require` made callable by its qualified name. It binds no
    /// name, so no lookup by name can meet it.
    RequiredMacro(FunctionId),
    /// A `require` of a module, whether or not it has macros. It binds no
    /// name, so no lookup by name can meet it.
    RequiredModule(ModuleId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Binding {
    entry: Entry,
    prev: Namespace,
}

#[derive(Debug, Default)]
pub struct NamespaceStore {
    bindings: Vec<Binding>,
    by_binding: crate::fast_hash::HashMap<Binding, Namespace>,
    /// The splice bindings made on each head under each name. A splice is
    /// bound by what its value says, not where its value was built, so a value
    /// built again binds the namespace it bound before.
    splices: crate::fast_hash::HashMap<(Namespace, String), Vec<Namespace>>,
    prelude_head: Namespace,
}

impl NamespaceStore {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bind(&mut self, head: Namespace, name: impl Into<String>, symbol: NamespaceSymbol) -> Namespace {
        let name = name.into();
        let NamespaceSymbol::Splice(value) = &symbol else {
            return self.push(
                head,
                Entry::Named {
                    name,
                    symbol,
                    imported_from: None,
                },
            );
        };
        if let Some(bound) = self.equal_splice(head, &name, value) {
            return bound;
        }
        let key = (head, name.clone());
        let bound = self.push(
            head,
            Entry::Named {
                name,
                symbol,
                imported_from: None,
            },
        );
        self.splices.entry(key).or_default().push(bound);
        bound
    }

    fn equal_splice(&self, head: Namespace, name: &str, value: &QuotedSourceRoot) -> Option<Namespace> {
        let candidates = self.splices.get(&(head, name.to_string()))?;
        candidates.iter().copied().find(|&candidate| {
            matches!(
                &self.bindings[candidate.0 as usize - 1].entry,
                Entry::Named { symbol: NamespaceSymbol::Splice(bound), .. } if bound.semantically_eq(value, Horizon::Full)
            )
        })
    }

    /// Binds `name` to a callable `import` took from `module`.
    pub fn bind_import(
        &mut self,
        head: Namespace,
        name: impl Into<String>,
        symbol: NamespaceSymbol,
        module: ModuleId,
    ) -> Namespace {
        self.push(
            head,
            Entry::Named {
                name: name.into(),
                symbol,
                imported_from: Some(module),
            },
        )
    }

    /// `head`, with every binding an earlier import of `module` made retired
    /// when there is one, so the import about to be bound replaces it.
    pub fn replace_imports_of(&mut self, head: Namespace, module: ModuleId) -> Namespace {
        let imported = self
            .entries(head)
            .any(|entry| matches!(entry, Entry::Named { imported_from: Some(from), .. } if *from == module));
        if imported {
            self.push(head, Entry::ImportsReplaced(module))
        } else {
            head
        }
    }

    /// Records that `macro_function` may be called by its qualified name from
    /// `head` on.
    pub fn bind_required_macro(&mut self, head: Namespace, macro_function: FunctionId) -> Namespace {
        self.push(head, Entry::RequiredMacro(macro_function))
    }

    /// Records that `module` was `require`d from `head` on.
    pub fn bind_required_module(&mut self, head: Namespace, module: ModuleId) -> Namespace {
        self.push(head, Entry::RequiredModule(module))
    }

    fn push(&mut self, head: Namespace, entry: Entry) -> Namespace {
        let binding = Binding { entry, prev: head };
        if let Some(&id) = self.by_binding.get(&binding) {
            return id;
        }
        let id = BindingId(self.bindings.len() as u32 + 1);
        self.bindings.push(binding.clone());
        self.by_binding.insert(binding, id);
        id
    }

    /// The chain's entries from `head` back to its start, newest first.
    fn entries(&self, head: Namespace) -> impl Iterator<Item = &Entry> {
        std::iter::successors((!head.is_end()).then_some(head), |&link| {
            let prev = self.bindings[link.0 as usize - 1].prev;
            (!prev.is_end()).then_some(prev)
        })
        .map(|link| &self.bindings[link.0 as usize - 1].entry)
    }

    /// The modules `require`d in the chain from `head`, newest first.
    pub fn required_modules(&self, head: Namespace) -> impl Iterator<Item = ModuleId> {
        self.entries(head).filter_map(|entry| match entry {
            Entry::RequiredModule(module) => Some(*module),
            Entry::Named { .. } | Entry::RequiredMacro(_) | Entry::ImportsReplaced(_) => None,
        })
    }

    /// The chain's live named bindings from `head`, newest first: the ones a
    /// later import of the same module has not replaced.
    pub fn named(&self, head: Namespace) -> impl Iterator<Item = (&str, &NamespaceSymbol)> {
        let mut replaced: Vec<ModuleId> = Vec::new();
        self.entries(head).filter_map(move |entry| match entry {
            Entry::Named {
                name,
                symbol,
                imported_from,
            } => match imported_from {
                Some(module) if replaced.contains(module) => None,
                _ => Some((name.as_str(), symbol)),
            },
            Entry::ImportsReplaced(module) => {
                replaced.push(*module);
                None
            }
            Entry::RequiredMacro(_) | Entry::RequiredModule(_) => None,
        })
    }

    pub fn lookup(&self, head: Namespace, name: &str) -> Option<&NamespaceSymbol> {
        self.named(head)
            .find_map(|(bound, symbol)| (bound == name).then_some(symbol))
    }

    /// Whether `require` made `macro_function` callable by its qualified name
    /// in the chain from `head`.
    pub fn is_required_macro(&self, head: Namespace, macro_function: FunctionId) -> bool {
        self.entries(head)
            .any(|entry| matches!(entry, Entry::RequiredMacro(required) if *required == macro_function))
    }

    /// Whether any named binding in the chain from `head` carries a symbol
    /// `predicate` accepts.
    pub fn any_symbol(&self, head: Namespace, mut predicate: impl FnMut(&NamespaceSymbol) -> bool) -> bool {
        self.named(head).any(|(_, symbol)| predicate(symbol))
    }

    pub fn lookup_matching(
        &self,
        head: Namespace,
        name: &str,
        mut predicate: impl FnMut(&NamespaceSymbol) -> bool,
    ) -> Option<&NamespaceSymbol> {
        self.named(head)
            .find_map(|(bound, symbol)| (bound == name && predicate(symbol)).then_some(symbol))
    }

    pub fn lookup_best_matching<T: Ord>(
        &self,
        head: Namespace,
        name: &str,
        mut score: impl FnMut(&NamespaceSymbol) -> Option<T>,
    ) -> Option<&NamespaceSymbol> {
        let mut best: Option<(T, &NamespaceSymbol)> = None;
        for (bound, symbol) in self.named(head) {
            if bound != name {
                continue;
            }
            if let Some(candidate) = score(symbol)
                && best.as_ref().is_none_or(|(current, _)| candidate > *current)
            {
                best = Some((candidate, symbol));
            }
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
