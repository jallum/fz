//! The roots of a receive clause.
//!
//! A clause binds variables, and variables overlap: `[_, head | tail]` binds the
//! cell and the head and tail inside it. A send that wins the receive hands the
//! receiver the clause's roots, the outermost subjects its arguments read, and
//! the receiver reads every argument out of them. Roots are disjoint positions
//! of the message, so copying each once copies nothing twice, and an argument
//! read out of a root is a view of the same cell the root is.

use super::PatternDispatchPlan;
use crate::dispatch_matrix::{ProjectionKind, SubjectId, SubjectSource};
use smallvec::SmallVec;

/// The subjects a clause's arguments are read from, and where each argument
/// sits below its root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OutcomeRoots {
    /// The roots, in the order the first argument that reads each one names it.
    pub(crate) roots: Vec<SubjectId>,
    /// One per argument, in argument order.
    pub(crate) arguments: Vec<ArgumentRoot>,
}

/// One argument: the root it is read from and the subjects between them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ArgumentRoot {
    /// An index into [`OutcomeRoots::roots`].
    pub(crate) root: usize,
    /// The subjects from just below the root down to the argument, outermost
    /// first. Empty when the argument is its root.
    pub(crate) path: SmallVec<[SubjectId; 4]>,
}

impl OutcomeRoots {
    /// Whether the arguments are the roots, one for one and in order: nothing
    /// is left to project.
    pub(crate) fn is_identity(&self) -> bool {
        self.roots.len() == self.arguments.len()
            && self
                .arguments
                .iter()
                .enumerate()
                .all(|(index, argument)| argument.root == index && argument.path.is_empty())
    }
}

fn is_structural(kind: &ProjectionKind) -> bool {
    matches!(
        kind,
        ProjectionKind::TupleField(_)
            | ProjectionKind::StructField(_)
            | ProjectionKind::ListHead
            | ProjectionKind::ListTail
    )
}

impl<TypeHandle> PatternDispatchPlan<TypeHandle> {
    /// The roots of a clause whose arguments read `arguments`.
    ///
    /// An argument's root is the outermost argument subject on its chain of
    /// structural projections (tuple field, struct field, list head, list
    /// tail), whose reads are fixed offsets the receiver repeats. A bitstring
    /// field and a map value end the chain: the sender already extracted the
    /// value, so the value is its own root.
    pub(crate) fn outcome_roots(&self, arguments: impl IntoIterator<Item = SubjectId> + Clone) -> OutcomeRoots {
        let mut roots: Vec<SubjectId> = Vec::new();
        let mut paths = Vec::new();
        for argument in arguments.clone() {
            let mut chain: SmallVec<[SubjectId; 6]> = SmallVec::new();
            chain.push(argument);
            let mut at = argument;
            while let SubjectSource::Projection(projection) = self.subject(at) {
                if !is_structural(&projection.kind) {
                    break;
                }
                at = projection.source;
                chain.push(at);
            }
            let outermost = chain
                .iter()
                .rposition(|subject| arguments.clone().into_iter().any(|argument| argument == *subject))
                .expect("an argument is on its own chain");
            let root = chain[outermost];
            let index = roots.iter().position(|known| *known == root).unwrap_or_else(|| {
                roots.push(root);
                roots.len() - 1
            });
            paths.push(ArgumentRoot {
                root: index,
                path: chain[..outermost].iter().rev().copied().collect(),
            });
        }
        OutcomeRoots {
            roots,
            arguments: paths,
        }
    }
}
