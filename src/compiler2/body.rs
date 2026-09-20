//! Compiler2's function-local lowered body vocabulary.
//!
//! A lowered body keeps clause shape, stable local value ids, callsite ids,
//! pattern/destructure steps, and compiler-generated lambda definitions, but
//! it stops above old-world CPS IR and planner concerns.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{BinOp, BitType, Endian, TypeExprBody, UnOp};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::fz_ir::{ExternAbi, ExternReturn, ExternTy};
use crate::ground_value::GroundValue;
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

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq, Hash)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub ownership: crate::fz_ir::OwnershipMode,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LoweredExtern {
    pub abi: ExternAbi,
    pub symbol: String,
    pub params: Vec<ExternTy>,
    pub variadic: bool,
    pub ret: ExternReturn,
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

pub(crate) fn step_defined_values(step: &LoweredStep) -> impl Iterator<Item = ValueId> {
    let values = match step {
        LoweredStep::Const { value, .. }
        | LoweredStep::Tuple { value, .. }
        | LoweredStep::List { value, .. }
        | LoweredStep::Map { value, .. }
        | LoweredStep::MapUpdate { value, .. }
        | LoweredStep::Struct { value, .. }
        | LoweredStep::Bitstring { value, .. }
        | LoweredStep::FunctionRef { value, .. }
        | LoweredStep::Lambda { value, .. }
        | LoweredStep::BinaryOp { value, .. }
        | LoweredStep::UnaryOp { value, .. }
        | LoweredStep::MapIndex { value, .. }
        | LoweredStep::FieldAccess { value, .. }
        | LoweredStep::RequireMapValue { value, .. }
        | LoweredStep::TupleField { value, .. }
        | LoweredStep::BitstringInit { reader: value, .. } => [Some(*value), None, None],
        LoweredStep::SplitList { head, tail, .. } => [Some(*head), Some(*tail), None],
        LoweredStep::BitstringRead {
            ok, value, next_reader, ..
        } => [Some(*ok), Some(*value), Some(*next_reader)],
        LoweredStep::AssertLiteral { .. }
        | LoweredStep::AssertStruct { .. }
        | LoweredStep::AssertTuple { .. }
        | LoweredStep::AssertEmptyList { .. }
        | LoweredStep::AssertSame { .. }
        | LoweredStep::AssertBitstringDone { .. } => [None; 3],
    };
    values.into_iter().flatten()
}

pub(crate) fn step_used_values(step: &LoweredStep, out: &mut Vec<ValueId>) {
    match step {
        LoweredStep::Const { .. } | LoweredStep::FunctionRef { .. } => {}
        LoweredStep::Tuple { items, .. } => out.extend(items.iter().map(|item| item.value)),
        LoweredStep::List { items, tail, .. } => {
            out.extend(items.iter().copied());
            if let Some(tail) = tail {
                out.push(*tail);
            }
        }
        LoweredStep::Map { entries, .. } => {
            for (key, value) in entries {
                out.push(key.value);
                out.push(*value);
            }
        }
        LoweredStep::MapUpdate { base, entries, .. } => {
            out.push(*base);
            for (key, value) in entries {
                out.push(key.value);
                out.push(*value);
            }
        }
        LoweredStep::Struct { fields, .. } => out.extend(fields.iter().map(|(_, value)| *value)),
        LoweredStep::Bitstring { fields, .. } => {
            for field in fields {
                out.push(field.value);
                if let Some(LoweredBitSize::Value(size)) = field.spec.size {
                    out.push(size);
                }
            }
        }
        LoweredStep::Lambda { captures, .. } => out.extend(captures.iter().copied()),
        LoweredStep::BinaryOp { left, right, .. } => {
            out.push(*left);
            out.push(*right);
        }
        LoweredStep::UnaryOp { input, .. } => {
            out.push(*input);
        }
        LoweredStep::MapIndex { base, key, .. } => {
            out.push(*base);
            out.push(key.value);
        }
        LoweredStep::FieldAccess { base, .. } | LoweredStep::AssertStruct { source: base, .. } => {
            out.push(*base);
        }
        LoweredStep::RequireMapValue { source, .. } => {
            out.push(*source);
        }
        LoweredStep::AssertLiteral { source, .. }
        | LoweredStep::AssertTuple { source, .. }
        | LoweredStep::AssertEmptyList { source } => {
            out.push(*source);
        }
        LoweredStep::TupleField { source, .. } => {
            out.push(*source);
        }
        LoweredStep::AssertSame { source, value } => {
            out.push(*source);
            out.push(*value);
        }
        LoweredStep::SplitList { source, .. } => {
            out.push(*source);
        }
        LoweredStep::BitstringInit { source, .. } | LoweredStep::AssertBitstringDone { reader: source } => {
            out.push(*source);
        }
        LoweredStep::BitstringRead { reader, spec, .. } => {
            out.push(*reader);
            if let Some(LoweredBitSize::Value(size)) = spec.size {
                out.push(size);
            }
        }
    }
}

pub(crate) fn tail_used_values(tail: &LoweredTail, out: &mut Vec<ValueId>) {
    match tail {
        LoweredTail::Value { value, .. } => {
            out.push(*value);
        }
        LoweredTail::DirectCall { args, .. } => {
            for arg in args {
                out.push(arg.value);
            }
        }
        LoweredTail::ClosureCall { callee, args, .. } => {
            out.push(*callee);
            for arg in args {
                out.push(arg.value);
            }
        }
        LoweredTail::If { cond, .. } => {
            out.push(*cond);
        }
        LoweredTail::Dispatch { inputs, bindings, .. } => {
            out.extend(inputs.iter().copied());
            out.extend(bindings.pinned.iter().copied());
            out.extend(bindings.prepared.iter().copied());
        }
        LoweredTail::Receive(receive) => {
            let bindings = &receive.bindings;
            let after = &receive.after;
            out.extend(bindings.pinned.iter().copied());
            out.extend(bindings.prepared.iter().copied());
            if let Some(after) = after {
                out.push(after.timeout);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
}

/// Where one step sits in a lowered body: in a clause's projections, or in a
/// control entry's steps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum StepSite {
    Projection { clause: u32, index: u32 },
    Entry { entry: ControlEntryId, index: u32 },
}

/// What one run of steps defines, uses and retains.
///
/// `used` and `retained` carry the position of the step that asks for the
/// value, so a query can start at any step; a tail's uses sit at the step
/// count, past every step, which is where a reader starting mid-run still
/// meets them.
#[derive(Debug, Clone, Default)]
struct StepUses {
    defined: Vec<(u32, ValueId)>,
    used: Vec<(u32, ValueId)>,
    retained: Vec<(u32, ValueId)>,
}

impl StepUses {
    fn of(steps: &[LoweredStep], tail: Option<&LoweredTail>) -> Self {
        let mut table = Self::default();
        let mut operands = Vec::new();
        for (index, step) in steps.iter().enumerate() {
            table
                .defined
                .extend(step_defined_values(step).map(|value| (index as u32, value)));
            operands.clear();
            step_used_values(step, &mut operands);
            table.used.extend(operands.iter().map(|value| (index as u32, *value)));
        }
        if let Some(tail) = tail {
            operands.clear();
            tail_used_values(tail, &mut operands);
            table
                .used
                .extend(operands.iter().map(|value| (steps.len() as u32, *value)));
        }
        table
    }

    fn used_from(&self, first_step: u32) -> impl Iterator<Item = ValueId> + '_ {
        positions_from(&self.used, first_step)
    }

    fn retained_from(&self, first_step: u32) -> impl Iterator<Item = ValueId> + '_ {
        positions_from(&self.retained, first_step)
    }
}

fn positions_from(positions: &[(u32, ValueId)], first_step: u32) -> impl Iterator<Item = ValueId> + '_ {
    let start = positions.partition_point(|(step, _)| *step < first_step);
    positions[start..].iter().map(|(_, value)| *value)
}

/// A clause body's definition and use tables, recorded as its steps join the
/// body.
///
/// Ownership construction asks the same two questions over and over -- where
/// is this value defined, and does any later step use it -- and answering
/// either by searching the body makes the passes cubic in the constructions
/// they analyse. The tables answer both in constant or output-proportional
/// time.
///
/// `LoweredBody::clauses` is the only way to build a clause body, so no body
/// exists without tables that agree with its steps, and nothing downstream
/// rebuilds them. Later edits to a step change its ownership modes or its list
/// retention, never which values it defines or names as operands; retention is
/// the one edit that adds a use, and `LoweredBody::retain_list_source` writes
/// the step and the table together.
///
/// The tables are a function of the clauses and entries alone, which is why
/// two bodies with equal steps are equal bodies -- comparing tables would only
/// re-ask a question the steps have already answered.
#[derive(Debug, Clone)]
pub struct BodyTables {
    definitions: HashMap<ValueId, StepSite>,
    projections: Vec<StepUses>,
    entries: Vec<StepUses>,
}

impl PartialEq for BodyTables {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}

impl BodyTables {
    fn of(clauses: &[LoweredClause], entries: &[LoweredEntry]) -> Self {
        let projections = clauses
            .iter()
            .map(|clause| StepUses::of(&clause.projections, None))
            .collect::<Vec<_>>();
        let entry_uses = entries
            .iter()
            .map(|entry| StepUses::of(&entry.steps, Some(&entry.tail)))
            .collect::<Vec<_>>();
        let mut definitions = HashMap::new();
        for (clause, table) in projections.iter().enumerate() {
            for (index, value) in &table.defined {
                definitions.entry(*value).or_insert(StepSite::Projection {
                    clause: clause as u32,
                    index: *index,
                });
            }
        }
        for (entry, table) in entry_uses.iter().enumerate() {
            for (index, value) in &table.defined {
                definitions.entry(*value).or_insert(StepSite::Entry {
                    entry: ControlEntryId::from_u32(entry as u32),
                    index: *index,
                });
            }
        }
        Self {
            definitions,
            projections,
            entries: entry_uses,
        }
    }

    /// The values this entry's steps at or after `first_step`, and its tail,
    /// name as operands. Duplicates ride along; a caller that pays per value
    /// dedups.
    pub(crate) fn entry_uses_from(&self, entry: ControlEntryId, first_step: u32) -> impl Iterator<Item = ValueId> + '_ {
        self.entries[entry.as_u32() as usize].used_from(first_step)
    }

    /// The sources whose ownership this entry's list steps at or after
    /// `first_step` retain.
    pub(crate) fn entry_retentions_from(
        &self,
        entry: ControlEntryId,
        first_step: u32,
    ) -> impl Iterator<Item = ValueId> + '_ {
        self.entries[entry.as_u32() as usize].retained_from(first_step)
    }

    pub(crate) fn entry_defines(&self, entry: ControlEntryId) -> impl Iterator<Item = ValueId> + '_ {
        self.entries[entry.as_u32() as usize]
            .defined
            .iter()
            .map(|(_, value)| *value)
    }

    pub(crate) fn clause_defines(&self, clause: usize) -> impl Iterator<Item = ValueId> + '_ {
        self.projections[clause].defined.iter().map(|(_, value)| *value)
    }

    pub(crate) fn clause_uses(&self, clause: usize) -> impl Iterator<Item = ValueId> + '_ {
        self.projections[clause].used_from(0)
    }
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
        tables: BodyTables,
    },
}

impl LoweredBody {
    /// The one way to build a clause body: the tables are recorded here, from
    /// the steps themselves, so they cannot disagree with what they index.
    pub(crate) fn clauses(clauses: Vec<LoweredClause>, entries: Vec<LoweredEntry>, generated: Vec<FunctionId>) -> Self {
        let tables = BodyTables::of(&clauses, &entries);
        Self::Clauses {
            clauses,
            entries,
            generated,
            tables,
        }
    }

    /// The step that defines `value`, or `None` when the value arrives as a
    /// clause parameter, an entry parameter or a dispatch outcome argument.
    pub(crate) fn value_definition(&self, value: ValueId) -> Option<&LoweredStep> {
        let Self::Clauses {
            clauses,
            entries,
            tables,
            ..
        } = self
        else {
            return None;
        };
        match tables.definitions.get(&value)? {
            StepSite::Projection { clause, index } => Some(&clauses[*clause as usize].projections[*index as usize]),
            StepSite::Entry { entry, index } => Some(&entries[entry.as_u32() as usize].steps[*index as usize]),
        }
    }

    /// Record that a list step rebuilds `source`, taking a share of its
    /// ownership. The step and the use table move together because the
    /// retention is a use of `source` that the step did not carry when it
    /// joined the body.
    pub(crate) fn retain_list_source(
        &mut self,
        entry: ControlEntryId,
        step: usize,
        source: ValueId,
        permission: crate::fz_ir::ListRewritePermission,
    ) {
        let Self::Clauses { entries, tables, .. } = self else {
            panic!("only a clause body holds list constructions")
        };
        let LoweredStep::List { retention, .. } = &mut entries[entry.as_u32() as usize].steps[step] else {
            panic!("a retention belongs to a list construction")
        };
        *retention = Some(crate::fz_ir::ListRetention { source, permission });
        let retained = &mut tables.entries[entry.as_u32() as usize].retained;
        let position = retained.partition_point(|(recorded, _)| *recorded < step as u32);
        retained.insert(position, (step as u32, source));
    }

    /// Narrow or widen what a recorded list retention may do with its source.
    /// The source is unchanged, so the tables stand.
    pub(crate) fn set_list_rewrite_permission(
        &mut self,
        entry: ControlEntryId,
        step: usize,
        permission: crate::fz_ir::ListRewritePermission,
    ) {
        let Self::Clauses { entries, .. } = self else {
            panic!("only a clause body holds list constructions")
        };
        let LoweredStep::List {
            retention: Some(retention),
            ..
        } = &mut entries[entry.as_u32() as usize].steps[step]
        else {
            panic!("a permission belongs to a recorded retention")
        };
        retention.permission = permission;
    }
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
    pub physical_captures: Vec<ValueId>,
    pub physical_params: Vec<ValueId>,
    pub steps: Vec<LoweredStep>,
    pub tail: LoweredTail,
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
pub struct DispatchBindings<V = ValueId> {
    pub pinned: Vec<V>,
    pub prepared: Vec<V>,
}

impl<V> Default for DispatchBindings<V> {
    fn default() -> Self {
        Self {
            pinned: Vec::new(),
            prepared: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ControlDispatch {
    pub(crate) plan: Rc<PatternDispatchPlan<Ty>>,
    pub(crate) outcomes: Vec<OutcomeEdge>,
    pub(crate) miss_entry: ControlEntryId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OutcomeEdge {
    pub(crate) target: ControlEntryId,
    pub(crate) arguments: Box<[OutcomeArgument]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OutcomeArgument {
    pub(crate) subject: crate::dispatch_matrix::SubjectId,
    pub(crate) parameter: ValueId,
    pub(crate) role: ValueRole,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ValueRole {
    Semantic,
    Physical,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum SubjectOriginRoot {
    Value(ValueId),
    MailboxMessage(ControlEntryId),
}

impl ControlDispatch {
    pub(crate) fn new(
        plan: Rc<PatternDispatchPlan<Ty>>,
        outcomes: Vec<OutcomeEdge>,
        miss_entry: ControlEntryId,
    ) -> Self {
        assert_eq!(
            outcomes.len(),
            plan.outcomes.len(),
            "an inline dispatch owns one target slot per plan outcome"
        );
        Self {
            plan,
            outcomes,
            miss_entry,
        }
    }

    pub(crate) fn outcome(&self, outcome: crate::dispatch_matrix::OutcomeId) -> &OutcomeEdge {
        self.outcomes
            .get(outcome.0 as usize)
            .expect("every winning outcome has one target edge")
    }
}

impl LoweredTail {
    pub(crate) fn outcome_edges(&self) -> &[OutcomeEdge] {
        match self {
            Self::Dispatch { dispatch, .. } => &dispatch.outcomes,
            Self::Receive(receive) => &receive.outcomes,
            _ => &[],
        }
    }

    pub(crate) fn outcome_edges_mut(&mut self) -> &mut [OutcomeEdge] {
        match self {
            Self::Dispatch { dispatch, .. } => &mut dispatch.outcomes,
            Self::Receive(receive) => &mut receive.outcomes,
            _ => &mut [],
        }
    }

    pub(crate) fn dispatch_plan(&self) -> &PatternDispatchPlan<Ty> {
        match self {
            Self::Dispatch { dispatch, .. } => &dispatch.plan,
            Self::Receive(receive) => &receive.dispatch,
            _ => panic!("a subject borrows its owning dispatch"),
        }
    }
}

impl LoweredBody {
    pub(crate) fn dispatch_subject_origin(
        &self,
        owner: ControlEntryId,
        mut subject: crate::dispatch_matrix::SubjectId,
    ) -> (SubjectOriginRoot, Vec<&crate::dispatch_matrix::ProjectionKind>) {
        let Self::Clauses { entries, .. } = self else {
            panic!("an outcome belongs to a clause body")
        };
        let tail = &entries[owner.as_u32() as usize].tail;
        let mut path = Vec::new();
        loop {
            match tail.dispatch_plan().subject(subject) {
                crate::dispatch_matrix::SubjectSource::Input { ordinal } => {
                    path.reverse();
                    let root = match tail {
                        LoweredTail::Dispatch { inputs, .. } => SubjectOriginRoot::Value(inputs[*ordinal as usize]),
                        LoweredTail::Receive(_) => {
                            assert_eq!(*ordinal, 0, "receive has one mailbox message input");
                            SubjectOriginRoot::MailboxMessage(owner)
                        }
                        _ => unreachable!(),
                    };
                    return (root, path);
                }
                crate::dispatch_matrix::SubjectSource::Projection(projection) => {
                    path.push(&projection.kind);
                    subject = projection.source;
                }
            }
        }
    }
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
    pub(crate) outcomes: Vec<OutcomeEdge>,
    pub after: Option<ReceiveAfter>,
    pub dest: ControlDestination,
    pub(crate) dispatch: Rc<PatternDispatchPlan<Ty>>,
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

/// A lowered map key position: the runtime value, plus the compile-time
/// constant when the source wrote a literal. Map keys are VALUES — the
/// carried literal is what lets analysis type the field precisely without
/// singleton numeric types in the lattice (mirroring `RequireMapValue`).
#[derive(Debug, Clone, PartialEq)]
pub struct LoweredMapKey {
    pub value: ValueId,
    pub literal: Option<GroundValue>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LoweredStep {
    Const {
        value: ValueId,
        literal: GroundValue,
    },
    Tuple {
        value: ValueId,
        items: Vec<crate::fz_ir::OwnershipUse<ValueId>>,
    },
    List {
        value: ValueId,
        items: Vec<ValueId>,
        tail: Option<ValueId>,
        retention: Option<crate::fz_ir::ListRetention<ValueId>>,
    },
    Map {
        value: ValueId,
        entries: Vec<(LoweredMapKey, ValueId)>,
        quoted_span: Option<Span>,
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
        literal: GroundValue,
    },
    AssertStruct {
        source: ValueId,
        module: ModuleId,
    },
    RequireMapValue {
        value: ValueId,
        source: ValueId,
        key: GroundValue,
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
    Lowered(Rc<LoweredBody>),
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
        let next = BodyState::Lowered(Rc::new(body));
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
