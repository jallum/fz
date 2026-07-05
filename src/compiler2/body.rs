//! Compiler2's function-local lowered body vocabulary.
//!
//! A lowered body keeps clause shape, stable local value ids, callsite ids,
//! pattern/destructure steps, and compiler-generated lambda definitions, but
//! it stops above old-world CPS IR and planner concerns.

use std::collections::{HashMap, HashSet};

use crate::ast::{BinOp, BitType, Endian, TypeExprBody, UnOp};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::fz_ir::ExternTy;
use crate::source::Span;
use crate::type_expr::ResolvedSpecDecl;

use super::identity::{FunctionId, ModuleId};
use super::types::Ty;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub reusable_cons_captures: Vec<ReusableConsCapture>,
    pub steps: Vec<LoweredStep>,
    pub tail: LoweredTail,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReusableConsCapture {
    pub head: ValueId,
    pub source: ValueId,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ControlEntryOrigin {
    Clause,
    Branch,
    ReceiveOutcome,
    DeliveredResume { value: ValueId },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DeliveredValueSource {
    LocalValue(ValueId),
    CallsiteReturn(CallSiteId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DeliveredValueJoin {
    pub value: ValueId,
    pub sources: Vec<DeliveredValueSource>,
}

impl ControlEntryOrigin {
    pub fn input_value(&self) -> Option<ValueId> {
        match self {
            Self::Clause | Self::Branch | Self::ReceiveOutcome => None,
            Self::DeliveredResume { value } => Some(*value),
        }
    }
}

pub(crate) fn delivered_value_joins(body: &LoweredBody) -> HashMap<ControlEntryId, DeliveredValueJoin> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return HashMap::new();
    };
    let mut delivered_values = HashMap::new();
    for (entry_index, entry) in entries.iter().enumerate() {
        if let ControlEntryOrigin::DeliveredResume { value } = entry.origin {
            delivered_values.insert(ControlEntryId::from_u32(entry_index as u32), value);
        }
    }
    let mut sources = HashMap::<ControlEntryId, Vec<DeliveredValueSource>>::new();
    for entry in entries {
        collect_tail_deliveries(&entry.tail, &delivered_values, &mut sources);
    }
    sources
        .into_iter()
        .filter_map(|(entry, mut sources)| {
            let value = delivered_values.get(&entry).copied()?;
            sources.sort_by_key(delivered_value_source_sort_key);
            sources.dedup();
            Some((entry, DeliveredValueJoin { value, sources }))
        })
        .collect()
}

/// The set of local values a body actually reads (consumes) in any step or
/// tail. This is a deterministic static artifact of the lowered body — it does
/// not depend on demand convergence or evaluation schedule — so it is a
/// reliable consumption signal where the demand lattice would under-report a
/// value whose downstream consumer is itself under-demanded.
pub(crate) fn body_consumed_values(body: &LoweredBody) -> HashSet<ValueId> {
    let mut consumed = HashSet::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return consumed;
    };
    for clause in clauses {
        for step in &clause.projections {
            collect_step_reads(step, &mut consumed);
        }
    }
    for entry in entries {
        consumed.extend(entry.captures.iter().copied());
        consumed.extend(entry.reusable_cons_captures.iter().map(|cons| cons.source));
        for step in &entry.steps {
            collect_step_reads(step, &mut consumed);
        }
        collect_tail_reads(&entry.tail, &mut consumed);
    }
    consumed
}

fn collect_step_reads(step: &LoweredStep, consumed: &mut HashSet<ValueId>) {
    match step {
        LoweredStep::Const { .. } | LoweredStep::FunctionRef { .. } => {}
        LoweredStep::Tuple { items, .. } => consumed.extend(items.iter().copied()),
        LoweredStep::List { items, tail, .. } => {
            consumed.extend(items.iter().copied());
            consumed.extend(tail.iter().copied());
        }
        LoweredStep::Map { entries, .. } => {
            for (key, value) in entries {
                consumed.insert(key.value);
                consumed.insert(*value);
            }
        }
        LoweredStep::MapUpdate { base, entries, .. } => {
            consumed.insert(*base);
            for (key, value) in entries {
                consumed.insert(key.value);
                consumed.insert(*value);
            }
        }
        LoweredStep::Struct { fields, .. } => consumed.extend(fields.iter().map(|(_, value)| *value)),
        LoweredStep::Bitstring { fields, .. } => {
            for field in fields {
                consumed.insert(field.value);
                if let Some(LoweredBitSize::Value(size)) = field.spec.size {
                    consumed.insert(size);
                }
            }
        }
        LoweredStep::Lambda { captures, .. } => consumed.extend(captures.iter().copied()),
        LoweredStep::BinaryOp { left, right, .. } => {
            consumed.insert(*left);
            consumed.insert(*right);
        }
        LoweredStep::UnaryOp { input, .. } => {
            consumed.insert(*input);
        }
        LoweredStep::MapIndex { base, key, .. } => {
            consumed.insert(*base);
            consumed.insert(key.value);
        }
        LoweredStep::FieldAccess { base, .. } => {
            consumed.insert(*base);
        }
        LoweredStep::AssertLiteral { source, .. }
        | LoweredStep::AssertStruct { source, .. }
        | LoweredStep::RequireMapValue { source, .. }
        | LoweredStep::AssertTuple { source, .. }
        | LoweredStep::TupleField { source, .. }
        | LoweredStep::AssertEmptyList { source }
        | LoweredStep::SplitList { source, .. }
        | LoweredStep::BitstringInit { source, .. } => {
            consumed.insert(*source);
        }
        LoweredStep::AssertSame { source, value } => {
            consumed.insert(*source);
            consumed.insert(*value);
        }
        LoweredStep::BitstringRead { reader, spec, .. } => {
            consumed.insert(*reader);
            if let Some(LoweredBitSize::Value(size)) = spec.size {
                consumed.insert(size);
            }
        }
        LoweredStep::AssertBitstringDone { reader } => {
            consumed.insert(*reader);
        }
    }
}

fn collect_tail_reads(tail: &LoweredTail, consumed: &mut HashSet<ValueId>) {
    match tail {
        LoweredTail::Value { value, .. } => {
            consumed.insert(*value);
        }
        LoweredTail::DirectCall { args, .. } => consumed.extend(args.iter().map(|arg| arg.value)),
        LoweredTail::ClosureCall { callee, args, .. } => {
            consumed.insert(*callee);
            consumed.extend(args.iter().map(|arg| arg.value));
        }
        LoweredTail::If { cond, .. } => {
            consumed.insert(*cond);
        }
        LoweredTail::Dispatch { inputs, bindings, .. } => {
            consumed.extend(inputs.iter().copied());
            consumed.extend(bindings.pinned.iter().copied());
            consumed.extend(bindings.prepared.iter().copied());
        }
        LoweredTail::Receive(receive) => {
            if let Some(after) = &receive.after {
                consumed.insert(after.timeout);
            }
            consumed.extend(receive.bindings.pinned.iter().copied());
            consumed.extend(receive.bindings.prepared.iter().copied());
        }
        LoweredTail::Halt { .. } => {}
    }
}

fn collect_tail_deliveries(
    tail: &LoweredTail,
    delivered_values: &HashMap<ControlEntryId, ValueId>,
    out: &mut HashMap<ControlEntryId, Vec<DeliveredValueSource>>,
) {
    match tail {
        LoweredTail::Value {
            value,
            dest: ControlDestination::Deliver(entry),
        } if delivered_values.contains_key(entry) => {
            out.entry(*entry)
                .or_default()
                .push(DeliveredValueSource::LocalValue(*value));
        }
        LoweredTail::DirectCall {
            callsite,
            dest: ControlDestination::Deliver(entry),
            ..
        }
        | LoweredTail::ClosureCall {
            callsite,
            dest: ControlDestination::Deliver(entry),
            ..
        } if delivered_values.contains_key(entry) => {
            out.entry(*entry)
                .or_default()
                .push(DeliveredValueSource::CallsiteReturn(*callsite));
        }
        _ => {}
    }
}

fn delivered_value_source_sort_key(source: &DeliveredValueSource) -> String {
    format!("{source:?}")
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

/// How a callsite's positional args map onto its callee's semantic input
/// space. A direct call's args ARE the callee's inputs, one-for-one; a
/// closure call's args follow a capture prefix supplied by the closure
/// itself, so they land at `callee_input_len - arg_count + arg_index`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CallInputMode {
    Direct,
    Closure,
}

impl CallInputMode {
    /// The callee-side semantic input index fed by this callsite's
    /// `arg_index`'th argument, or `None` if the callsite is malformed for
    /// this mode (more closure args than the callee has inputs, or a direct
    /// arg beyond the callee's arity).
    pub fn semantic_index(self, callee_input_len: usize, arg_count: usize, arg_index: usize) -> Option<usize> {
        match self {
            CallInputMode::Direct => (arg_index < callee_input_len).then_some(arg_index),
            CallInputMode::Closure => callee_input_len
                .checked_sub(arg_count)
                .map(|capture_prefix| capture_prefix + arg_index),
        }
    }
}

/// The `CallInputMode` of every callsite in `body`, keyed by `CallSiteId`.
///
/// A `LoweredBody`'s `entries` arena holds exactly the control-flow nodes
/// reachable from its clauses' entries: lowering only ever pushes an entry
/// while planning a `Deliver` resume, an `If` branch, a `Dispatch` arm/miss,
/// or a `Receive` clause/after (see `jobs::body::plan_block` and its call
/// sites). So a flat scan of `entries` visits exactly the same callsites, in
/// the same modes, that a recursive walk following those same
/// `ControlDestination`/branch links from the clause entries would visit —
/// and does it without recursion or having to hand-enumerate every tail
/// variant's destinations.
///
/// This "`entries` == the set reachable from the clause entries" invariant is
/// what makes the flat scan sound, and it has TWO producers that must both
/// preserve it: `jobs::body::plan_block` (the original lowering) and
/// `jobs::artifact::prune_lowered_body` (the pruned/reindexed body `transport`
/// substitutes for a materialized executable). A future change to either that
/// left a dangling or orphaned entry would silently break this scan.
pub(crate) fn callsite_input_modes(body: &LoweredBody) -> HashMap<CallSiteId, CallInputMode> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body else {
        return out;
    };
    for entry in entries {
        match &entry.tail {
            LoweredTail::DirectCall { callsite, .. } => {
                out.insert(*callsite, CallInputMode::Direct);
            }
            LoweredTail::ClosureCall { callsite, .. } => {
                out.insert(*callsite, CallInputMode::Closure);
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Halt { .. } => {}
        }
    }
    out
}

/// The positional call args of every callsite in `body`, keyed by
/// `CallSiteId`. A callsite's args are a direct field of the `DirectCall`/
/// `ClosureCall` tail that names it -- never accumulated along a walk -- so
/// this rides the same flat scan over `entries` as `callsite_input_modes`
/// (see that function's doc comment for the reachability invariant that
/// makes the flat scan sound).
pub(crate) fn callsite_call_args(body: &LoweredBody) -> HashMap<CallSiteId, Vec<CallArg>> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body else {
        return out;
    };
    for entry in entries {
        if let LoweredTail::DirectCall { callsite, args, .. } | LoweredTail::ClosureCall { callsite, args, .. } =
            &entry.tail
        {
            out.insert(*callsite, args.clone());
        }
    }
    out
}

/// The `ControlDestination` every callsite in `body` delivers its result to,
/// keyed by `CallSiteId`. Same reasoning as `callsite_call_args`: a
/// callsite's destination is a direct field of its own tail, not something
/// accumulated from the entries downstream of it, so the flat scan over
/// `entries` is equivalent to a recursive walk of the destination graph.
pub(crate) fn callsite_call_dests(body: &LoweredBody) -> HashMap<CallSiteId, ControlDestination> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body else {
        return out;
    };
    for entry in entries {
        if let LoweredTail::DirectCall { callsite, dest, .. } | LoweredTail::ClosureCall { callsite, dest, .. } =
            &entry.tail
        {
            out.insert(*callsite, dest.clone());
        }
    }
    out
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
