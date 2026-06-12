use super::namespace::Namespace;
use super::quoted_surface::ScopeSurface;
use super::source::{Horizon, QuotedSourceRoot};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CodeId(u32);

impl CodeId {
    pub const ZERO: Self = Self(0);

    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone)]
pub enum CodeState {
    Pending,
    /// Compiler-owned quoted source is the authority. The decoded scope surface
    /// is a compiler2-owned read model derived from that quoted root.
    Indexed {
        source: QuotedCodeSource,
    },
    /// Imports resolved and top-level names bound; records the resulting namespace.
    Scoped {
        source: QuotedCodeSource,
        namespace: Namespace,
    },
}

#[derive(Debug, Clone)]
pub struct QuotedCodeSource {
    pub quoted: QuotedSourceRoot,
    pub surface: ScopeSurface,
}

#[derive(Debug, Default)]
pub struct CodeMap {
    slots: Vec<CodeState>,
    names: Vec<Option<String>>,
    texts: Vec<String>,
}

impl CodeMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, name: Option<String>, text: String) -> CodeId {
        let id = CodeId(self.slots.len() as u32);
        self.slots.push(CodeState::Pending);
        self.names.push(name);
        self.texts.push(text);
        id
    }

    pub fn index(&mut self, id: CodeId, source: QuotedCodeSource) -> bool {
        let slot = &mut self.slots[id.0 as usize];
        let next = CodeState::Indexed { source };
        let changed = !same_code_state(slot, &next);
        *slot = next;
        changed
    }

    pub fn scope(&mut self, id: CodeId, namespace: Namespace) -> bool {
        let slot = &mut self.slots[id.0 as usize];
        let source = match slot {
            CodeState::Indexed { source } | CodeState::Scoped { source, .. } => source.clone(),
            CodeState::Pending => panic!("code must be indexed before scoping"),
        };
        let changed = !matches!(&*slot, CodeState::Scoped { namespace: n, .. } if *n == namespace);
        *slot = CodeState::Scoped { source, namespace };
        changed
    }

    pub fn get(&self, id: CodeId) -> &CodeState {
        self.slots
            .get(id.0 as usize)
            .expect("code ids should be known before reading code slots")
    }

    pub fn name(&self, id: CodeId) -> Option<&str> {
        self.names
            .get(id.0 as usize)
            .expect("code ids should be known before reading names")
            .as_deref()
    }

    pub fn text(&self, id: CodeId) -> &str {
        self.texts
            .get(id.0 as usize)
            .map(String::as_str)
            .expect("code ids should have source text")
    }

    pub fn ids(&self) -> Vec<CodeId> {
        (0..self.slots.len()).map(|index| CodeId(index as u32)).collect()
    }

    pub(crate) fn len(&self) -> usize {
        self.slots.len()
    }
}

fn same_code_state(left: &CodeState, right: &CodeState) -> bool {
    match (left, right) {
        (CodeState::Pending, CodeState::Pending) => true,
        (CodeState::Indexed { source: l }, CodeState::Indexed { source: r })
        | (CodeState::Scoped { source: l, .. }, CodeState::Scoped { source: r, .. }) => {
            // Code identity is its module surface — bodies belong to their own
            // per-function facts, so a body-only edit does not move it.
            l.quoted.semantically_eq(&r.quoted, Horizon::Surface)
        }
        _ => false,
    }
}
