//! Exact, source-owned transport edges into one executable input.

use std::collections::HashSet;
use std::rc::Rc;

use super::body::ValueId;
use super::identity::ExecutableKey;
use super::semantic::{JoinContribution, SemanticOrd};
use super::types::Types;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InputSlot {
    pub executable: ExecutableKey,
    pub semantic_index: usize,
}

impl SemanticOrd<Types> for InputSlot {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        self.executable
            .semantic_cmp(&other.executable, types)
            .then_with(|| self.semantic_index.cmp(&other.semantic_index))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IncomingInputSource {
    pub producer: ExecutableKey,
    pub value: ValueId,
    pub role: IncomingInputRole,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IncomingInputRole {
    CallArgument,
    CallableCapture {
        construction: ValueId,
        capture_index: usize,
    },
}

impl SemanticOrd<Types> for IncomingInputSource {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        self.producer
            .semantic_cmp(&other.producer, types)
            .then_with(|| self.value.as_u32().cmp(&other.value.as_u32()))
            .then_with(|| self.role.cmp(&other.role))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct IncomingInputSources(pub Rc<[IncomingInputSource]>);

impl IncomingInputSources {
    pub(crate) fn new(sources: HashSet<IncomingInputSource>, types: &Types) -> Self {
        let mut sources = sources.into_iter().collect::<Vec<_>>();
        sources.sort_by(|left, right| left.semantic_cmp(right, types));
        Self(sources.into())
    }
}

impl JoinContribution for IncomingInputSources {
    type Ctx = Types;

    fn bottom() -> Self {
        Self::default()
    }

    fn join_assign(&mut self, other: &Self, types: &mut Types) {
        if other.0.is_empty() || self == other {
            return;
        }
        if self.0.is_empty() {
            self.0 = Rc::clone(&other.0);
            return;
        }
        let union = self.0.iter().chain(other.0.iter()).cloned().collect::<HashSet<_>>();
        if union.len() != self.0.len() {
            *self = Self::new(union, types);
        }
    }
}

#[cfg(test)]
#[path = "incoming_inputs_test.rs"]
mod incoming_inputs_test;
