//! AST-free executable matching representation.
//!
//! `Matcher` is the migration target for function clauses, `case`, `with`
//! else arms, receive probes, and guard-compatible helper functions. The
//! frontend may build it from AST patterns, but executable matcher data must
//! carry only subjects, constants, spans, tests, bindings, and outcomes.

use crate::diag::{FileId, Span};
use crate::fz_ir::Var;
use crate::types::Ty;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

pub type BodyId = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NodeId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct InputId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct PinnedId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Matcher {
    pub inputs: Vec<MatcherInput>,
    pub pinned: Vec<PinnedInput>,
    pub prepared_keys: Vec<MatcherConst>,
    pub nodes: Vec<MatcherNode>,
    pub root: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GuardDispatch {
    pub matcher: Matcher,
    pub bodies: Vec<GuardExpr>,
}

pub fn prepared_key_name(index: usize) -> String {
    format!("__matcher_key_{}", index)
}

pub fn map_value_subject(map: &SubjectRef, key: &MatcherConst) -> SubjectRef {
    SubjectRef::MapValue {
        map: Box::new(map.clone()),
        key: key.clone(),
    }
}

/// Rewrite `s.file` through `remap`; a `FileId` absent from the map (including
/// `FileId::NONE`/DUMMY) is left unchanged. The single source of span-remap
/// truth shared by `Matcher` and `Module::remap_file_ids`.
fn remap_span(s: &mut Span, remap: &HashMap<FileId, FileId>) {
    if let Some(&to) = remap.get(&s.file) {
        s.file = to;
    }
}

impl Matcher {
    pub fn node(&self, id: NodeId) -> Option<&MatcherNode> {
        self.nodes.get(id.0 as usize)
    }

    /// Rewrite every `Span.file` reachable from this matcher through `remap`.
    /// Covers input/pinned spans, every `MatcherNode` variant's span, and the
    /// leaf/binding spans. Used when a relocatably-loaded module's receive
    /// matchers are merged into a consumer's `SourceMap`.
    pub(crate) fn remap_file_ids(&mut self, remap: &HashMap<FileId, FileId>) {
        for input in &mut self.inputs {
            remap_span(&mut input.span, remap);
        }
        for pinned in &mut self.pinned {
            remap_span(&mut pinned.span, remap);
        }
        for node in &mut self.nodes {
            // Exhaustive: a future span-carrying variant must fail to compile,
            // not be silently skipped.
            match node {
                MatcherNode::Fail { span } => remap_span(span, remap),
                MatcherNode::Leaf(leaf) => {
                    remap_span(&mut leaf.span, remap);
                    for binding in &mut leaf.bindings {
                        remap_span(&mut binding.span, remap);
                    }
                }
                MatcherNode::Switch { span, .. } => remap_span(span, remap),
                MatcherNode::Test { span, .. } => remap_span(span, remap),
                MatcherNode::Guard { span, .. } => remap_span(span, remap),
            }
        }
    }

    /// Read-only twin of `remap_file_ids`: visits every `Span` reachable from
    /// this matcher, in the same exhaustive site inventory. Used to gather a
    /// receive matcher's referenced source files for portable IR units.
    pub(crate) fn visit_spans(&self, f: &mut impl FnMut(Span)) {
        for input in &self.inputs {
            f(input.span);
        }
        for pinned in &self.pinned {
            f(pinned.span);
        }
        for node in &self.nodes {
            // Exhaustive: a future span-carrying variant must fail to compile,
            // not be silently skipped.
            match node {
                MatcherNode::Fail { span } => f(*span),
                MatcherNode::Leaf(leaf) => {
                    f(leaf.span);
                    for binding in &leaf.bindings {
                        f(binding.span);
                    }
                }
                MatcherNode::Switch { span, .. } => f(*span),
                MatcherNode::Test { span, .. } => f(*span),
                MatcherNode::Guard { span, .. } => f(*span),
            }
        }
    }
}

#[cfg(test)]
impl Matcher {
    pub fn new(inputs: Vec<MatcherInput>, root: MatcherNode) -> Self {
        Self {
            inputs,
            pinned: Vec::new(),
            prepared_keys: Vec::new(),
            nodes: vec![root],
            root: NodeId(0),
        }
    }

    pub fn push_node(&mut self, node: MatcherNode) -> NodeId {
        let id = NodeId(self.nodes.len() as u32);
        self.nodes.push(node);
        id
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatcherInput {
    /// Optional IR var this input came from. Receive matchers use ABI inputs
    /// instead; inline case/function matchers usually retain the source var.
    pub var: Option<Var>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PinnedInput {
    pub name: String,
    pub var: Option<Var>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SubjectRef {
    Input(InputId),
    TupleField {
        tuple: Box<SubjectRef>,
        index: u32,
    },
    ListHead(Box<SubjectRef>),
    ListTail(Box<SubjectRef>),
    /// Value produced by a successful map entry lookup.
    ///
    /// This subject is path-local: it is valid only after the matcher has
    /// proven the entry is present on the current control-flow edge.
    MapValue {
        map: Box<SubjectRef>,
        key: MatcherConst,
    },
    BitstringField {
        bitstring: Box<SubjectRef>,
        index: u32,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum MatcherNode {
    Fail {
        span: Span,
    },
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
    Guard {
        expr: GuardExpr,
        on_true: NodeId,
        on_false: NodeId,
        span: Span,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatcherLeaf {
    pub body_id: BodyId,
    pub bindings: Vec<MatcherBinding>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatcherBinding {
    pub name: String,
    pub source: SubjectRef,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum GuardExpr {
    Const(MatcherConst),
    Subject(SubjectRef),
    Pinned(PinnedId),
    Unary {
        op: GuardUnaryOp,
        expr: Box<GuardExpr>,
    },
    Binary {
        op: GuardBinOp,
        lhs: Box<GuardExpr>,
        rhs: Box<GuardExpr>,
    },
    Dispatch {
        inputs: Vec<GuardExpr>,
        dispatch: Box<GuardDispatch>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum GuardUnaryOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum GuardBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Neq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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
    MapKind {
        subject: SubjectRef,
    },
    /// Presence test for a map entry.
    ///
    /// A successful edge may reuse the corresponding `SubjectRef::MapValue`.
    /// A failed edge must not inherit that value. Presence is not equivalent
    /// to `map_get(...) != nil`; a present key may legally hold `nil`.
    MapHasKey {
        subject: SubjectRef,
        key: MatcherConst,
    },
    Bitstring {
        subject: SubjectRef,
        fields: Vec<MatcherBitField>,
    },
    Type {
        subject: SubjectRef,
        ty: Ty,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatcherBitField {
    pub ty: MatcherBitType,
    pub size: Option<MatcherBitSize>,
    pub endian: MatcherEndian,
    pub signed: bool,
    pub unit: Option<u32>,
    /// Names bound directly to this extracted field value. Reader execution
    /// uses these for later dynamic sizes before leaf bindings are emitted.
    pub direct_bindings: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum MatcherBitSize {
    Literal(u32),
    BindingName(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MatcherBitType {
    Integer,
    Float,
    Binary,
    Bits,
    Utf8,
    Utf16,
    Utf32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MatcherEndian {
    Big,
    Little,
    Native,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
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
#[path = "matcher_test.rs"]
mod matcher_test;
