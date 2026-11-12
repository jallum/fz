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
    const EXACT: bool = true;

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
        let merged = self.merged_with(other, types);
        if merged.len() != self.0.len() {
            self.0 = merged.into();
        }
    }
}

impl IncomingInputSources {
    /// The union of two sources already in semantic order, in semantic order:
    /// one linear merge, so joining a contribution never re-sorts what both
    /// sides already hold in order.
    fn merged_with(&self, other: &Self, types: &Types) -> Vec<IncomingInputSource> {
        let (mut left, mut right) = (self.0.iter().peekable(), other.0.iter().peekable());
        let mut merged = Vec::with_capacity(self.0.len() + other.0.len());
        loop {
            let next = match (left.peek(), right.peek()) {
                (Some(l), Some(r)) => match l.semantic_cmp(r, types) {
                    std::cmp::Ordering::Less => left.next(),
                    std::cmp::Ordering::Greater => right.next(),
                    std::cmp::Ordering::Equal => {
                        let source = left.next();
                        if source == right.peek().copied() {
                            right.next();
                        }
                        source
                    }
                },
                (Some(_), None) => left.next(),
                (None, Some(_)) => right.next(),
                (None, None) => break,
            };
            merged.extend(next.cloned());
        }
        merged
    }
}

#[cfg(test)]
#[path = "incoming_inputs_test.rs"]
mod incoming_inputs_test;
