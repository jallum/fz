//! Compiler2's function-local lowered body vocabulary.
//!
//! A lowered body keeps clause shape, stable local value ids, callsite ids,
//! pattern/destructure steps, and compiler-generated lambda definitions, but
//! it stops above old-world CPS IR and planner concerns.

use crate::ast::{BinOp, UnOp};
use crate::compiler::source::Span;

use super::identity::FunctionId;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ValueId(u32);

impl ValueId {
    pub fn from_u32(value: u32) -> Self {
        Self(value)
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CallSiteId(u32);

impl CallSiteId {
    pub fn from_u32(value: u32) -> Self {
        Self(value)
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    Binary(Vec<u8>),
    Atom(String),
    Bool(bool),
    Nil,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DirectCallee {
    Function(FunctionId),
    Named { name: String, arity: usize },
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoweredBody {
    Extern {
        abi: String,
        arity: usize,
    },
    Clauses {
        clauses: Vec<LoweredClause>,
        generated: Vec<FunctionId>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoweredClause {
    pub span: Span,
    pub params: Vec<ValueId>,
    pub setup: Vec<LoweredStep>,
    pub guard: Option<LoweredBlock>,
    pub body: LoweredBlock,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoweredBlock {
    pub span: Span,
    pub steps: Vec<LoweredStep>,
    pub result: ValueId,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoweredStep {
    Const {
        value: ValueId,
        literal: Literal,
    },
    Tuple {
        value: ValueId,
        items: Vec<ValueId>,
    },
    List {
        value: ValueId,
        items: Vec<ValueId>,
        tail: Option<ValueId>,
    },
    FunctionRef {
        value: ValueId,
        function: FunctionId,
    },
    NamedFunctionRef {
        value: ValueId,
        name: String,
        arity: usize,
    },
    DirectCall {
        value: ValueId,
        callsite: CallSiteId,
        callee: DirectCallee,
        args: Vec<ValueId>,
    },
    ClosureCall {
        value: ValueId,
        callsite: CallSiteId,
        callee: ValueId,
        args: Vec<ValueId>,
    },
    Lambda {
        value: ValueId,
        function: FunctionId,
        captures: Vec<ValueId>,
    },
    BinaryOp {
        value: ValueId,
        op: BinOp,
        left: ValueId,
        right: ValueId,
    },
    UnaryOp {
        value: ValueId,
        op: UnOp,
        input: ValueId,
    },
    MapIndex {
        value: ValueId,
        base: ValueId,
        key: ValueId,
    },
    If {
        value: ValueId,
        cond: ValueId,
        then_block: LoweredBlock,
        else_block: LoweredBlock,
    },
    AssertLiteral {
        source: ValueId,
        literal: Literal,
    },
    AssertTuple {
        source: ValueId,
        arity: usize,
    },
    TupleField {
        value: ValueId,
        source: ValueId,
        index: usize,
    },
    AssertEmptyList {
        source: ValueId,
    },
    AssertSame {
        source: ValueId,
        value: ValueId,
    },
    SplitList {
        source: ValueId,
        head: ValueId,
        tail: ValueId,
    },
}

#[derive(Debug, Clone)]
pub struct BodySlot {
    pub(crate) state: BodyState,
    pub(crate) revision: u64,
}

#[derive(Debug, Clone)]
pub enum BodyState {
    Placeholder,
    Lowered(LoweredBody),
}

#[derive(Debug, Default)]
pub struct LoweredBodyMap {
    slots: Vec<BodySlot>,
}

impl LoweredBodyMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, id: FunctionId, body: LoweredBody) -> u64 {
        self.ensure(id);
        let slot = &mut self.slots[id.as_u32() as usize];
        let next = BodyState::Lowered(body);
        if !slot.state.same_state(&next) {
            slot.state = next;
            slot.revision += 1;
        }
        slot.revision
    }

    pub fn get(&self, id: FunctionId) -> Option<&BodySlot> {
        self.slots.get(id.as_u32() as usize)
    }

    fn ensure(&mut self, id: FunctionId) {
        let needed = id.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || BodySlot {
                state: BodyState::Placeholder,
                revision: 0,
            });
        }
    }
}

impl BodyState {
    fn same_state(&self, other: &Self) -> bool {
        match (self, other) {
            (BodyState::Placeholder, BodyState::Placeholder) => true,
            (BodyState::Lowered(left), BodyState::Lowered(right)) => left == right,
            _ => false,
        }
    }
}
