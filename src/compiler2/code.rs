use std::cell::RefCell;
use std::rc::Rc;

use super::namespace::Namespace;
use super::quoted_surface::ScopeSurface;
use super::source::{Horizon, QuotedSourceRoot};
use crate::source::SourceMap;

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq, Hash)]
pub struct SourceOwner(u32);

impl SourceOwner {
    pub fn as_u32(self) -> u32 {
        self.0
    }

    fn slot(self) -> usize {
        self.0 as usize
    }

    #[cfg(test)]
    pub(crate) const fn for_test(raw: u32) -> Self {
        Self(raw)
    }
}

#[derive(Debug, Clone)]
pub enum CodeState {
    /// A stable owner exists, but its immutable source has not been demanded.
    Reserved,
    Pending {
        version: crate::source::SourceVersion,
    },
    /// Compiler-owned quoted source is the authority. The decoded scope surface
    /// is a compiler2-owned read model derived from that quoted root.
    Indexed {
        version: crate::source::SourceVersion,
        source: QuotedCodeSource,
    },
    /// Imports resolved and top-level names bound; records the resulting namespace.
    Scoped {
        version: crate::source::SourceVersion,
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
    source_map: Rc<RefCell<SourceMap>>,
}

impl CodeMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, name: Option<String>, text: String) -> SourceOwner {
        let owner = SourceOwner(self.slots.len() as u32);
        let version = self.source_map.borrow_mut().add_code(name, text);
        self.slots.push(CodeState::Pending { version });
        owner
    }

    pub(crate) fn reserve(&mut self) -> SourceOwner {
        let owner = SourceOwner(self.slots.len() as u32);
        self.slots.push(CodeState::Reserved);
        owner
    }

    pub(crate) fn materialize(
        &mut self,
        owner: SourceOwner,
        name: Option<String>,
        text: String,
    ) -> crate::source::SourceVersion {
        let state = self
            .slots
            .get_mut(owner.slot())
            .expect("source owners must be reserved before materialization");
        assert!(matches!(state, CodeState::Reserved), "source owners materialize once");
        let version = self.source_map.borrow_mut().add_code(name, text);
        *state = CodeState::Pending { version };
        version
    }

    pub fn index(&mut self, id: SourceOwner, source: QuotedCodeSource) -> bool {
        assert!(
            self.version(id).is_some(),
            "source must be materialized before indexing"
        );
        let slot = &mut self.slots[id.slot()];
        let version = slot.version().expect("source must be materialized before indexing");
        let next = CodeState::Indexed { version, source };
        let changed = !same_code_state(slot, &next);
        *slot = next;
        changed
    }

    pub fn scope(&mut self, id: SourceOwner, namespace: Namespace) -> bool {
        let slot = &mut self.slots[id.slot()];
        let (version, source) = match slot {
            CodeState::Indexed { version, source } | CodeState::Scoped { version, source, .. } => {
                (*version, source.clone())
            }
            CodeState::Reserved => panic!("source must be materialized before scoping"),
            CodeState::Pending { .. } => panic!("source must be indexed before scoping"),
        };
        let changed = !matches!(&*slot, CodeState::Scoped { namespace: n, .. } if *n == namespace);
        *slot = CodeState::Scoped {
            version,
            source,
            namespace,
        };
        changed
    }

    pub fn get(&self, id: SourceOwner) -> &CodeState {
        self.slots
            .get(id.slot())
            .expect("source owners should be known before reading source slots")
    }

    pub fn version(&self, owner: SourceOwner) -> Option<crate::source::SourceVersion> {
        self.get(owner).version()
    }

    pub fn name(&self, owner: SourceOwner) -> Option<std::sync::Arc<str>> {
        let version = self.version(owner)?;
        self.source_map.borrow().code(version).name.clone()
    }

    pub fn text(&self, owner: SourceOwner) -> std::sync::Arc<str> {
        let version = self
            .version(owner)
            .expect("source owners should have a materialized version");
        self.source_map.borrow().code(version).bytes.clone()
    }

    pub fn ids(&self) -> Vec<SourceOwner> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(slot, state)| state.version().map(|_| SourceOwner(slot as u32)))
            .collect()
    }

    pub(crate) fn len(&self) -> usize {
        self.source_map.borrow().code_count()
    }

    pub(crate) fn source_map(&self) -> Rc<RefCell<SourceMap>> {
        self.source_map.clone()
    }
}

impl CodeState {
    fn version(&self) -> Option<crate::source::SourceVersion> {
        match self {
            Self::Reserved => None,
            Self::Pending { version } | Self::Indexed { version, .. } | Self::Scoped { version, .. } => Some(*version),
        }
    }
}

fn same_code_state(left: &CodeState, right: &CodeState) -> bool {
    match (left, right) {
        (CodeState::Pending { version: l }, CodeState::Pending { version: r }) => l == r,
        (CodeState::Reserved, CodeState::Reserved) => true,
        (CodeState::Indexed { version: lv, source: l }, CodeState::Indexed { version: rv, source: r })
        | (
            CodeState::Scoped {
                version: lv, source: l, ..
            },
            CodeState::Scoped {
                version: rv, source: r, ..
            },
        ) => {
            // Code identity is its module surface — bodies belong to their own
            // per-function facts, so a body-only edit does not move it.
            lv == rv && l.quoted.semantically_eq(&r.quoted, Horizon::Surface)
        }
        _ => false,
    }
}
