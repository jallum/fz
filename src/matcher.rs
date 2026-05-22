//! AST-free executable matching representation.
//!
//! `Matcher` is the migration target for function clauses, `case`, `with`
//! else arms, receive probes, and guard-compatible helper functions. The
//! frontend may build it from AST patterns, but executable matcher data must
//! carry only subjects, constants, spans, tests, bindings, and outcomes.

#![allow(dead_code)]

use crate::diag::Span;
use crate::fz_ir::Var;

pub type BodyId = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InputId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PinnedId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OutputSlot(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Matcher {
    pub inputs: Vec<MatcherInput>,
    pub pinned: Vec<PinnedInput>,
    pub nodes: Vec<MatcherNode>,
    pub root: NodeId,
}

impl Matcher {
    pub fn new(inputs: Vec<MatcherInput>, root: MatcherNode) -> Self {
        Self {
            inputs,
            pinned: Vec::new(),
            nodes: vec![root],
            root: NodeId(0),
        }
    }

    pub fn node(&self, id: NodeId) -> Option<&MatcherNode> {
        self.nodes.get(id.0 as usize)
    }

    pub fn push_node(&mut self, node: MatcherNode) -> NodeId {
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(node);
        id
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatcherInput {
    /// Optional IR var this input came from. Receive matchers use ABI inputs
    /// instead; inline case/function matchers usually retain the source var.
    pub var: Option<Var>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinnedInput {
    pub name: String,
    pub var: Option<Var>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubjectRef {
    Input(InputId),
    TupleField {
        tuple: Box<SubjectRef>,
        index: u32,
    },
    ListHead(Box<SubjectRef>),
    ListTail(Box<SubjectRef>),
    MapValue {
        map: Box<SubjectRef>,
        key: MatcherConst,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MatcherConst {
    Int(i64),
    FloatBits(u64),
    AtomName(String),
    Bool(bool),
    Nil,
    EmptyList,
    Utf8Binary(Vec<u8>),
    /// A pre-materialized heap value supplied outside matcher execution.
    PreparedKey(u32),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatcherNode {
    Fail { span: Span },
    Leaf(MatcherLeaf),
    Switch {
        subject: SubjectRef,
        kind: SwitchKind,
        cases: Vec<(SwitchKey, NodeId)>,
        default: NodeId,
        span: Span,
    },
    Test {
        test: MatcherTest,
        on_true: NodeId,
        on_false: NodeId,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatcherLeaf {
    pub body_id: BodyId,
    pub bindings: Vec<MatcherBinding>,
    pub preconditions: Vec<MatcherPrecondition>,
    pub guard: Option<GuardId>,
    pub on_guard_fail: Option<NodeId>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatcherBinding {
    pub name: String,
    pub source: SubjectRef,
    pub output: Option<OutputSlot>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatcherPrecondition {
    pub var: Var,
    pub ty: crate::types::Ty,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GuardId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatcherTest {
    EqConst {
        subject: SubjectRef,
        value: MatcherConst,
    },
    EqPinned {
        subject: SubjectRef,
        pinned: PinnedId,
    },
    TupleArity {
        subject: SubjectRef,
        arity: u32,
    },
    ListCons {
        subject: SubjectRef,
    },
    MapHasKey {
        subject: SubjectRef,
        key: MatcherConst,
    },
    Type {
        subject: SubjectRef,
        ty: crate::types::Ty,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SwitchKind {
    TupleArity,
    Atom,
    Int,
    Float,
    Bool,
    Nil,
    Binary,
    ListCons,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SwitchKey {
    Arity(u32),
    AtomName(String),
    Int(i64),
    FloatBits(u64),
    Bool(bool),
    Nil,
    Utf8Binary(Vec<u8>),
    EmptyList,
    Cons,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constructs_small_ast_free_matcher() {
        let input = MatcherInput {
            var: Some(Var(7)),
            span: Span::DUMMY,
        };
        let leaf = MatcherNode::Leaf(MatcherLeaf {
            body_id: 3,
            bindings: vec![MatcherBinding {
                name: "x".to_string(),
                source: SubjectRef::TupleField {
                    tuple: Box::new(SubjectRef::Input(InputId(0))),
                    index: 1,
                },
                output: Some(OutputSlot(0)),
                span: Span::DUMMY,
            }],
            preconditions: Vec::new(),
            guard: None,
            on_guard_fail: None,
            span: Span::DUMMY,
        });
        let matcher = Matcher::new(vec![input], leaf);

        assert_eq!(matcher.root, NodeId(0));
        let Some(MatcherNode::Leaf(leaf)) = matcher.node(matcher.root) else {
            panic!("expected root leaf");
        };
        assert_eq!(leaf.body_id, 3);
        assert_eq!(leaf.bindings[0].name, "x");
    }

    #[test]
    fn push_node_returns_stable_node_id() {
        let mut matcher = Matcher::new(
            vec![MatcherInput {
                var: None,
                span: Span::DUMMY,
            }],
            MatcherNode::Fail { span: Span::DUMMY },
        );
        let id = matcher.push_node(MatcherNode::Leaf(MatcherLeaf {
            body_id: 9,
            bindings: Vec::new(),
            preconditions: Vec::new(),
            guard: None,
            on_guard_fail: None,
            span: Span::DUMMY,
        }));

        assert_eq!(id, NodeId(1));
        assert!(matches!(
            matcher.node(id),
            Some(MatcherNode::Leaf(MatcherLeaf { body_id: 9, .. }))
        ));
    }

    #[test]
    fn matcher_module_does_not_import_ast_payloads() {
        let src = include_str!("matcher.rs");
        assert!(!src.contains(concat!("crate", "::", "ast")));
        assert!(!src.contains(concat!("Spanned", "<", "Pattern", ">")));
        assert!(!src.contains(concat!("Spanned", "<", "Expr", ">")));
    }
}
