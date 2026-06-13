//! Compiler2's function-local lowered body vocabulary.
//!
//! A lowered body keeps clause shape, stable local value ids, callsite ids,
//! pattern/destructure steps, and compiler-generated lambda definitions, but
//! it stops above old-world CPS IR and planner concerns.

use crate::ast::{BinOp, BitType, Endian, TypeExprBody, UnOp};
use crate::compiler::source::Span;
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::fz_ir::ExternTy;
use crate::type_expr::ResolvedSpecDecl;

use super::identity::{FunctionId, ModuleId};
use super::types::Ty;

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
pub struct CallSiteId {
    raw: u32,
    span: Span,
}

impl CallSiteId {
    pub fn new(raw: u32, span: Span) -> Self {
        Self { raw, span }
    }

    pub fn from_u32(value: u32) -> Self {
        Self::new(value, Span::DUMMY)
    }

    pub fn as_u32(self) -> u32 {
        self.raw
    }

    pub fn span(self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ControlEntryId(u32);

impl ControlEntryId {
    pub fn from_u32(value: u32) -> Self {
        Self(value)
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct CallArg {
    pub value: ValueId,
    pub ascription: Option<TypeExprBody>,
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

#[derive(Debug, Clone, PartialEq)]
pub struct LoweredExtern {
    pub abi: String,
    pub symbol: String,
    pub params: Vec<ExternTy>,
    pub variadic: bool,
    pub ret: ExternTy,
    pub return_ty: Ty,
    pub semantic_contract: ResolvedSpecDecl<Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoweredBitSize {
    Literal(u32),
    Value(ValueId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweredBitFieldSpec {
    pub ty: BitType,
    pub size: Option<LoweredBitSize>,
    pub endian: Endian,
    pub signed: bool,
    pub unit: Option<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LoweredBitField {
    pub value: ValueId,
    pub spec: LoweredBitFieldSpec,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoweredBody {
    Extern {
        signature: LoweredExtern,
    },
    Clauses {
        clauses: Vec<LoweredClause>,
        entries: Vec<LoweredEntry>,
        generated: Vec<FunctionId>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoweredClause {
    pub span: Span,
    pub params: Vec<ValueId>,
    pub projections: Vec<LoweredStep>,
    pub entry: ControlEntryId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoweredEntry {
    pub span: Span,
    pub origin: ControlEntryOrigin,
    pub params: Vec<ValueId>,
    pub captures: Vec<ValueId>,
    pub steps: Vec<LoweredStep>,
    pub tail: LoweredTail,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ControlEntryOrigin {
    Clause,
    Branch,
    ReceiveOutcome,
    DeliveredResume { value: ValueId },
    LocalResume { value: ValueId },
}

impl ControlEntryOrigin {
    pub fn input_value(&self) -> Option<ValueId> {
        match self {
            Self::Clause | Self::Branch | Self::ReceiveOutcome => None,
            Self::DeliveredResume { value } | Self::LocalResume { value } => Some(*value),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ControlDestination {
    Return,
    Deliver(ControlEntryId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct DispatchBindings {
    pub pinned: Vec<ValueId>,
    pub prepared: Vec<ValueId>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ControlDispatch {
    pub(crate) plan: PatternDispatchPlan<Ty>,
    pub(crate) arm_entries: Vec<ControlEntryId>,
    pub(crate) miss_entry: ControlEntryId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReceiveClause {
    pub span: Span,
    pub entry: ControlEntryId,
    pub bound_names: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReceiveAfter {
    pub span: Span,
    pub timeout: ValueId,
    pub entry: ControlEntryId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoweredReceive {
    pub bindings: DispatchBindings,
    pub clauses: Vec<ReceiveClause>,
    pub after: Option<ReceiveAfter>,
    pub dest: ControlDestination,
    pub(crate) dispatch: PatternDispatchPlan<Ty>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoweredTail {
    Value {
        value: ValueId,
        dest: ControlDestination,
    },
    DirectCall {
        value: ValueId,
        callsite: CallSiteId,
        callee: FunctionId,
        args: Vec<CallArg>,
        dest: ControlDestination,
    },
    ClosureCall {
        value: ValueId,
        callsite: CallSiteId,
        callee: ValueId,
        args: Vec<CallArg>,
        dest: ControlDestination,
    },
    If {
        cond: ValueId,
        then_entry: ControlEntryId,
        else_entry: ControlEntryId,
    },
    Dispatch {
        inputs: Vec<ValueId>,
        bindings: DispatchBindings,
        dispatch: Box<ControlDispatch>,
    },
    Receive(Box<LoweredReceive>),
    Halt {
        atom: String,
    },
}

/// A lowered map key position: the runtime value, plus the compile-time
/// constant when the source wrote a literal. Map keys are VALUES — the
/// carried literal is what lets analysis type the field precisely without
/// singleton numeric types in the lattice (mirroring `RequireMapValue`).
#[derive(Debug, Clone, PartialEq)]
pub struct LoweredMapKey {
    pub value: ValueId,
    pub literal: Option<Literal>,
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
    Map {
        value: ValueId,
        entries: Vec<(LoweredMapKey, ValueId)>,
    },
    MapUpdate {
        value: ValueId,
        base: ValueId,
        entries: Vec<(LoweredMapKey, ValueId)>,
    },
    Struct {
        value: ValueId,
        module: ModuleId,
        fields: Vec<(String, ValueId)>,
    },
    Bitstring {
        value: ValueId,
        fields: Vec<LoweredBitField>,
    },
    FunctionRef {
        value: ValueId,
        function: FunctionId,
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
        key: LoweredMapKey,
    },
    FieldAccess {
        value: ValueId,
        base: ValueId,
        field: String,
    },
    AssertLiteral {
        source: ValueId,
        literal: Literal,
    },
    AssertStruct {
        source: ValueId,
        module: ModuleId,
    },
    RequireMapValue {
        value: ValueId,
        source: ValueId,
        key: Literal,
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
    BitstringInit {
        reader: ValueId,
        source: ValueId,
    },
    BitstringRead {
        ok: ValueId,
        value: ValueId,
        next_reader: ValueId,
        reader: ValueId,
        spec: LoweredBitFieldSpec,
        is_last: bool,
    },
    AssertBitstringDone {
        reader: ValueId,
    },
}

#[derive(Debug, Clone)]
pub enum BodyState {
    Placeholder,
    Lowered(LoweredBody),
}

#[derive(Debug, Default)]
pub struct LoweredBodyMap {
    slots: Vec<BodyState>,
}

impl LoweredBodyMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, id: FunctionId, body: LoweredBody) -> bool {
        self.ensure(id);
        let slot = &mut self.slots[id.as_u32() as usize];
        let next = BodyState::Lowered(body);
        let changed = !slot.same_state(&next);
        *slot = next;
        changed
    }

    pub fn get(&self, id: FunctionId) -> Option<&BodyState> {
        self.slots.get(id.as_u32() as usize)
    }

    fn ensure(&mut self, id: FunctionId) {
        let needed = id.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || BodyState::Placeholder);
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
