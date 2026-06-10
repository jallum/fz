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
pub struct Code {
    pub(crate) state: CodeState,
}

#[derive(Debug, Clone)]
pub enum CodeState {
    Pending,
    /// Compiler-owned quoted source is the authority. The decoded scope surface
    /// is a compiler2-owned read model derived from that quoted root.
    Indexed {
        source: QuotedCodeSource,
    },
}

#[derive(Debug, Clone)]
pub struct QuotedCodeSource {
    pub quoted: QuotedSourceRoot,
    pub surface: ScopeSurface,
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
        });
        self.names.push(name);
        self.texts.push(text);
        id
    }

    pub fn index(&mut self, id: CodeId, source: QuotedCodeSource, current_revision: u64) -> u64 {
        let code = &mut self.slots[id.0 as usize];
        let next = CodeState::Indexed { source };
        let changed = !same_code_state(&code.state, &next);
        code.state = next;
        if changed {
            current_revision + 1
        } else {
            current_revision
        }
    }

    pub fn get(&self, id: CodeId) -> &Code {
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
        (CodeState::Indexed { source: left }, CodeState::Indexed { source: right }) => {
            // Code identity is its module surface — bodies belong to their own
            // per-function facts, so a body-only edit does not move it.
            left.quoted.semantically_eq(&right.quoted, Horizon::Surface)
        }
        _ => false,
    }
}
