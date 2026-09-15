use std::collections::HashMap;
use std::slice::from_raw_parts;

use super::backend::{
    backend_callable_identity, env_get, materialize_transport_value, transport_field_view, transport_field_views,
};
use super::*;
use crate::compiler2::transport::TransportStore;
use crate::compiler2::{BackendProgram, DispatchBindings, Ty, Types, ValueId};
use crate::dispatch_matrix::pattern::{
    PatternDispatchPlan, PatternGuardBinOp, PatternGuardExpr, PatternGuardUnaryOp, PatternPinnedInput,
};
use crate::dispatch_matrix::{
    BitstringEndian, BitstringFieldKind, BitstringFieldSize, BitstringShape, ComparisonValue, DispatchNode,
    EdgeEvidence, GraphNodeId, GroundValue, ListRegion, OutcomeId, PinnedValueId, ProjectionKind, Region, SubjectId,
    SubjectSource,
};
use crate::fz_ir::Module;
use crate::runtime_type_predicate::{
    RuntimeTypePredicate, RuntimeValueReader, TuplePositions, matches_runtime_type_predicate, surface_membership,
};
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, AnyValueRef, TRUE_ATOM_ID, ValueKind, struct_schema_id};
use fz_runtime::ir_runtime::{
    fz_bs_begin, fz_bs_field_spec, fz_bs_finalize, fz_bs_read_field_ref, fz_bs_reader_init_ref, fz_bs_write_field_ref,
    fz_list_head_ref, fz_list_tail_ref, fz_matcher_map_get_ref, fz_struct_get_field_ref,
};
use fz_runtime::procbin::{bitstring_bit_len, bitstring_byte_ptr, is_bitstring_like};
use fz_runtime::process::Process;

pub(super) type DispatchValues = crate::compiler2::DispatchBindings<AnyValue>;

/// Why a dispatch step produced no value.
///
/// The two reasons are not the same: a subject that does not match hands the
/// next edge its turn, while a question the executor cannot answer means the
/// plan and the values it was given disagree, and no edge can repair that.
#[derive(Debug)]
pub(super) enum DispatchStop {
    NoMatch,
    Broken(String),
}

impl DispatchStop {
    pub(super) fn broken(message: impl Into<String>) -> Self {
        Self::Broken(message.into())
    }
}

/// A result that is `Ok(None)` where the subject simply did not match, so a
/// caller can fall to its miss edge without swallowing a broken plan.
fn or_miss<T>(result: Result<T, DispatchStop>) -> Result<Option<T>, DispatchStop> {
    match result {
        Ok(value) => Ok(Some(value)),
        Err(DispatchStop::NoMatch) => Ok(None),
        Err(broken) => Err(broken),
    }
}

fn required<T>(value: Option<T>) -> Result<T, DispatchStop> {
    value.ok_or(DispatchStop::NoMatch)
}

/// Everything a dispatch run reads but never writes: the values it is deciding
/// about, the operands its pattern named, and the transport store that says how
/// a lane-form value is laid out.
///
/// An input reads `None` where the executable published no layout for it. The
/// plan's demand states which inputs it reads, and its own construction asserts
/// that every subject rides a charged input, so a `None` slot is one the walk
/// never asks about.
pub(super) struct DispatchOperands<'a> {
    pub(super) transport: &'a TransportStore,
    pub(super) inputs: &'a [Option<BackendBoundValue>],
    pub(super) pinned: &'a DispatchValues,
}

/// Where one door's pins and prepared keys come from.
///
/// An entry plan is handed the executable's decoded inputs: every pin it
/// carries was bound before its patterns began and arrives as one of those
/// inputs, and its prepared keys are materialised from the plan's own
/// constants. A match site names both as values its environment already holds.
pub(super) enum DispatchSource<'a> {
    Inputs(&'a [Option<BackendBoundValue>]),
    Bound {
        env: &'a HashMap<ValueId, BackendBoundValue>,
        bindings: &'a DispatchBindings,
    },
}

impl DispatchSource<'_> {
    /// The one runtime word a pin is compared against. A pin is compared whole,
    /// so its operand is always one word.
    fn pin(
        &self,
        transport: &TransportStore,
        proc: *mut Process,
        index: usize,
        pin: &PatternPinnedInput,
    ) -> Result<AnyValue, String> {
        match self {
            Self::Inputs(inputs) => pin
                .input
                .and_then(|ordinal| inputs.get(ordinal as usize))
                .and_then(Option::as_ref)
                .and_then(BackendBoundValue::runtime_word)
                .ok_or_else(|| format!("dispatch pin `{}` has no runtime argument operand", pin.name)),
            Self::Bound { env, bindings } => env_get(transport, proc, env, bindings.pinned[index]),
        }
    }

    /// The value one prepared key is looked up by.
    fn prepared_key(
        &self,
        transport: &TransportStore,
        proc: *mut Process,
        module: &Module,
        index: usize,
        key: &GroundValue,
    ) -> Result<AnyValue, String> {
        match self {
            Self::Inputs(_) => materialize_prepared_key(proc, module, key),
            Self::Bound { env, bindings } => env_get(transport, proc, env, bindings.prepared[index]),
        }
    }
}

/// The operands a plan needs beyond its inputs: one runtime word per pin it
/// compares against, and one per prepared key it looks up by.
///
/// A map pattern keyed by a binary -- `%{"name" => n}` -- is decided through a
/// PREPARED key: the executor finds the key's index in `plan.prepared_keys` and
/// reads the materialised value out of these. Only binary keys need it. Ints,
/// floats, atoms, booleans and nil are decided from the constant directly and
/// never consult prepared values.
pub(super) fn dispatch_values(
    proc: *mut Process,
    transport: &TransportStore,
    module: &Module,
    plan: &PatternDispatchPlan<Ty>,
    source: DispatchSource<'_>,
) -> Result<DispatchValues, String> {
    if let DispatchSource::Bound { bindings, .. } = &source {
        assert_eq!(
            bindings.pinned.len(),
            plan.pinned.len(),
            "a match site names every pin its plan carries"
        );
        assert_eq!(
            bindings.prepared.len(),
            plan.prepared_keys.len(),
            "a match site names every prepared key its plan carries"
        );
    }
    let mut prepared = Vec::with_capacity(plan.prepared_keys.len());
    for (index, key) in plan.prepared_keys.iter().enumerate() {
        prepared.push(source.prepared_key(transport, proc, module, index, key)?);
    }
    let mut pinned = Vec::with_capacity(plan.pinned.len());
    for (index, pin) in plan.pinned.iter().enumerate() {
        pinned.push(source.pin(transport, proc, index, pin)?);
    }
    Ok(DispatchValues { pinned, prepared })
}

/// The runtime value a prepared key is looked up by. A binary key is built here
/// because the plan carries only its bytes.
fn materialize_prepared_key(proc: *mut Process, module: &Module, key: &GroundValue) -> Result<AnyValue, String> {
    use crate::ground_value::DispatchShape;
    if let Some(DispatchShape::Utf8Binary(bytes)) = key.as_dispatch_shape() {
        let ref_word = fz_runtime::ir_runtime::fz_alloc_bitstring_const(
            proc,
            bytes.as_ptr() as u64,
            bytes.len() as u64,
            (bytes.len() * 8) as u64,
        );
        return interp_value_from_ref_word(ref_word, "prepared dispatch key");
    }
    dispatch_const_to_value(proc, module, key)
        .ok_or_else(|| format!("cannot materialize prepared dispatch key {key:?}"))
}

/// What the walk has learned about the subjects it has already produced.
#[derive(Default, Clone)]
struct DispatchExecState {
    values: HashMap<SubjectId, BackendBoundValue>,
}

/// One run of one dispatch plan against one set of operands.
///
/// The run holds the evidence it gathers, so the caller that asked it to decide
/// reads the winning outcome's arguments from the same run, off the same
/// operands the decision was made on.
pub(super) struct Dispatch<'a> {
    runtime: &'a mut IrInterpRuntime,
    types: &'a Types,
    program: &'a BackendProgram,
    module: &'a Module,
    plan: &'a PatternDispatchPlan<Ty>,
    operands: DispatchOperands<'a>,
    state: DispatchExecState,
}

impl<'a> Dispatch<'a> {
    pub(super) fn new(
        runtime: &'a mut IrInterpRuntime,
        types: &'a Types,
        program: &'a BackendProgram,
        module: &'a Module,
        plan: &'a PatternDispatchPlan<Ty>,
        operands: DispatchOperands<'a>,
    ) -> Self {
        Self {
            runtime,
            types,
            program,
            module,
            plan,
            operands,
            state: DispatchExecState::default(),
        }
    }

    /// Decide the plan. `Ok(None)` is a subject that matched no clause, which
    /// every caller answers for itself; an error is a plan the executor and its
    /// operands disagree about.
    ///
    /// A decision is a value: only the [`Decided`] this returns can be asked
    /// what the winning outcome bound, and it holds the run that produced it.
    pub(super) fn run(mut self) -> Result<Option<Decided<'a>>, String> {
        match self.node(self.plan.graph.root) {
            Ok(outcome) => Ok(Some(Decided { run: self, outcome })),
            Err(DispatchStop::NoMatch) => Ok(None),
            Err(DispatchStop::Broken(error)) => Err(error),
        }
    }

    /// Walk one node. A test decides its region against a copy of the evidence
    /// so far, and only the branch that is taken keeps what the test learned.
    fn node(&mut self, node_id: GraphNodeId) -> Result<OutcomeId, DispatchStop> {
        let plan = self.plan;
        match required(plan.graph.node(node_id))? {
            DispatchNode::Fail => Err(DispatchStop::NoMatch),
            DispatchNode::Outcome { outcome, .. } => Ok(*outcome),
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let before = self.state.clone();
                let took_match = self.region_hit(predicate.subject, &predicate.region, &on_match.evidence)?
                    && or_miss(self.apply_edge_evidence(&on_match.evidence))?.is_some();
                if took_match {
                    self.node(on_match.target)
                } else {
                    self.state = before;
                    self.node(on_miss.target)
                }
            }
        }
    }

    fn apply_edge_evidence(&mut self, evidence: &EdgeEvidence<Ty>) -> Result<(), DispatchStop> {
        for projection in &evidence.projections {
            if self.state.values.contains_key(projection) {
                continue;
            }
            let value = self.resolve_subject(*projection)?;
            self.state.values.insert(*projection, value);
        }
        Ok(())
    }

    /// The one runtime word a subject denotes.
    ///
    /// A tuple's arity, its field projections and a type test all read a subject
    /// in the lane form its caller delivered. What is left are the questions
    /// that want the whole value and cannot be decomposed: a pinned equality, a
    /// guard, and the map, list and bitstring regions. Those build the value
    /// here, at the question that asks for it, and keep it for the rest of this
    /// branch.
    fn subject_word(&mut self, subject: SubjectId) -> Result<AnyValue, DispatchStop> {
        let value = self.resolve_subject(subject)?;
        self.word_of(subject, value)
    }

    /// The same answer for a caller that has already resolved the subject.
    fn word_of(&mut self, subject: SubjectId, value: BackendBoundValue) -> Result<AnyValue, DispatchStop> {
        let word = match value {
            BackendBoundValue::Runtime(value) => return Ok(value),
            BackendBoundValue::Absent => {
                return Err(DispatchStop::broken(format!(
                    "dispatch subject {subject:?} carries no runtime value"
                )));
            }
            BackendBoundValue::Transport { shape, lanes } => {
                materialize_transport_value(self.operands.transport, self.proc(), shape, &lanes)
                    .map_err(DispatchStop::broken)?
            }
        };
        self.state.values.insert(subject, BackendBoundValue::Runtime(word));
        Ok(word)
    }

    /// What a subject holds, in whatever form it already has.
    ///
    /// A tuple field of a lane-form subject is a view over lanes the caller
    /// already delivered, so reading it allocates nothing. Every other
    /// projection reads through a runtime value.
    fn resolve_subject(&mut self, subject: SubjectId) -> Result<BackendBoundValue, DispatchStop> {
        if let Some(value) = self.state.values.get(&subject) {
            return Ok(value.clone());
        }
        let plan = self.plan;
        let proc = self.proc();
        let subject_data = required(plan.matrix.subjects.get(subject.0 as usize))?;
        let value = match &subject_data.source {
            SubjectSource::Input { ordinal } => match self.operands.inputs.get(*ordinal as usize).cloned().flatten() {
                Some(value) => value,
                None => {
                    return Err(DispatchStop::broken(format!(
                        "dispatch reads input {ordinal}, which did not arrive"
                    )));
                }
            },
            SubjectSource::Projection(projection) => match &projection.kind {
                ProjectionKind::TupleField(index) => {
                    let parent = self.resolve_subject(projection.source)?;
                    match transport_tuple_field(self.operands.transport, &parent, *index as usize)? {
                        Some(field) => field,
                        None => {
                            let parent = self.subject_word(projection.source)?;
                            let parent_slot = required(parent.value(proc).ok())?;
                            if parent_slot.kind() != ValueKind::STRUCT {
                                return Err(DispatchStop::NoMatch);
                            }
                            let field = required(
                                with_value_ref(proc, parent, "dispatch tuple field", |struct_ref| {
                                    fz_struct_get_field_ref(proc, struct_ref, index * 8)
                                })
                                .ok()
                                .and_then(|ref_word| interp_value_from_ref_word(ref_word, "dispatch tuple field").ok()),
                            )?;
                            BackendBoundValue::Runtime(field)
                        }
                    }
                }
                ProjectionKind::StructField(field) => {
                    let parent = self.subject_word(projection.source)?;
                    let parent = required(parent.as_ref_word(proc).ok())?;
                    let parent = required(AnyValueRef::from_raw_word(parent).ok())?;
                    let value = required(unsafe { &*proc }.heap.read_struct_named_field_ref(parent, field).ok())?;
                    BackendBoundValue::Runtime(required(
                        interp_value_from_ref_word(value.raw_word(), "dispatch struct field").ok(),
                    )?)
                }
                ProjectionKind::ListHead => {
                    let parent = self.subject_word(projection.source)?;
                    BackendBoundValue::Runtime(required(interp_list_head(proc, parent).ok())?)
                }
                ProjectionKind::ListTail => {
                    let parent = self.subject_word(projection.source)?;
                    BackendBoundValue::Runtime(required(interp_list_tail(proc, parent).ok())?)
                }
                ProjectionKind::MapValue { key } => {
                    let map = self.subject_word(projection.source)?;
                    BackendBoundValue::Runtime(required(self.map_lookup(map, key))?)
                }
                ProjectionKind::BitstringField(_) => return Err(DispatchStop::NoMatch),
            },
        };
        self.state.values.insert(subject, value.clone());
        Ok(value)
    }

    /// Decide one region question about one subject.
    ///
    /// A subject that cannot be produced fails its test, so the next edge gets
    /// its turn; only a plan the executor cannot answer stops the run.
    fn region_hit(
        &mut self,
        subject: SubjectId,
        region: &Region<Ty>,
        evidence: &EdgeEvidence<Ty>,
    ) -> Result<bool, DispatchStop> {
        match region {
            Region::Type(ty) => {
                // The value is asked in the form it is held: a tuple delivered
                // as lanes is decided per position, without one being built.
                let Some(value) = self.subject_bound_value(subject)? else {
                    return Ok(false);
                };
                let predicate = self.types.runtime_type_predicate(ty);
                self.type_matches(&predicate, &value)
            }
            Region::Equal(ComparisonValue::Const(value)) => {
                let Some(word) = self.subject_value(subject)? else {
                    return Ok(false);
                };
                Ok(dispatch_const_eq(self.proc(), self.module, word, value))
            }
            Region::Equal(ComparisonValue::Pinned(pin_id)) => {
                let Some(word) = self.subject_value(subject)? else {
                    return Ok(false);
                };
                Ok(self
                    .pin_value(*pin_id)
                    .is_some_and(|want| interp_value_eq(self.proc(), want, word).unwrap_or(false)))
            }
            Region::TupleArity(arity) => {
                let Some(value) = self.subject_bound_value(subject)? else {
                    return Ok(false);
                };
                // A lane-form subject knows its own arity: the transport shape
                // its caller delivered settles the question, with no value to
                // inspect.
                if let BackendBoundValue::Transport { shape, .. } = &value
                    && let Some(known) = self.operands.transport.interners().tuple_arity(*shape)
                {
                    return Ok(known == *arity as usize);
                }
                let Some(word) = or_miss(self.word_of(subject, value))? else {
                    return Ok(false);
                };
                let Ok(word) = word.value(self.proc()) else {
                    return Ok(false);
                };
                if word.kind() != ValueKind::STRUCT {
                    return Ok(false);
                }
                let Some(heap) = word.heap_addr() else {
                    return Ok(false);
                };
                Ok(unsafe { struct_schema_id(heap) } == interp_tuple_schema_id(self.runtime, *arity as usize))
            }
            Region::List(ListRegion::Empty) => {
                let Some(word) = self.subject_value(subject)? else {
                    return Ok(false);
                };
                Ok(word.is_empty_list())
            }
            Region::List(ListRegion::Cons) => {
                let Some(word) = self.subject_value(subject)? else {
                    return Ok(false);
                };
                Ok(word.value(self.proc()).ok().is_some_and(interp_is_list_cons))
            }
            Region::MapKind => {
                let Some(word) = self.subject_value(subject)? else {
                    return Ok(false);
                };
                Ok(word.value(self.proc()).ok().is_some_and(is_map_value))
            }
            Region::MapKeyPresent { key } => {
                let Some(map) = self.subject_value(subject)? else {
                    return Ok(false);
                };
                let Some(value) = self.map_lookup(map, key) else {
                    return Ok(false);
                };
                let plan = self.plan;
                for result in &evidence.projections {
                    if let SubjectSource::Projection(projection) = plan.subject(*result)
                        && projection.source == subject
                        && matches!(&projection.kind, ProjectionKind::MapValue { key: projection_key } if projection_key == key)
                    {
                        self.state.values.insert(*result, BackendBoundValue::Runtime(value));
                    }
                }
                Ok(true)
            }
            Region::Bitstring(shape) => {
                let Some(word) = self.subject_value(subject)? else {
                    return Ok(false);
                };
                let Ok(value) = word.value(self.proc()) else {
                    return Ok(false);
                };
                Ok(self.read_bitstring(value, shape))
            }
            Region::Guard(guard) => {
                let plan = self.plan;
                let Some(expr) = plan.guards.get(guard.0 as usize) else {
                    return Ok(false);
                };
                let Some(value) = or_miss(self.eval_guard(expr))? else {
                    return Ok(false);
                };
                Ok(!(value.is_false() || value.is_nil()))
            }
        }
    }

    /// The subject's runtime word, or `None` where it cannot be produced and the
    /// region therefore fails.
    fn subject_value(&mut self, subject: SubjectId) -> Result<Option<AnyValue>, DispatchStop> {
        or_miss(self.subject_word(subject))
    }

    /// The subject in whatever form it is held, or `None` where it cannot be
    /// produced and the region therefore fails.
    fn subject_bound_value(&mut self, subject: SubjectId) -> Result<Option<BackendBoundValue>, DispatchStop> {
        or_miss(self.resolve_subject(subject))
    }

    /// Ask a type test of a value in whatever form it is held.
    ///
    /// A whole value is offered to the shared matcher. A tuple held as lanes has
    /// no heap object to read a schema off, so it asks the predicate what it
    /// wants of a tuple of that arity and puts one question to each position
    /// instead -- the same decomposition the boxed matcher makes, one level in,
    /// against lanes the caller already delivered.
    ///
    /// A position carries runtime demand and so keeps a lane, which is why the
    /// absent arm below is unreachable rather than a case to answer.
    fn type_matches(
        &mut self,
        predicate: &RuntimeTypePredicate,
        value: &BackendBoundValue,
    ) -> Result<bool, DispatchStop> {
        let transport = self.operands.transport;
        let (shape, lanes) = match value {
            BackendBoundValue::Runtime(word) => return Ok(self.whole_value_matches(predicate, *word)),
            BackendBoundValue::Absent => {
                return Err(DispatchStop::broken(
                    "backend type test has no value to ask".to_string(),
                ));
            }
            BackendBoundValue::Transport { shape, lanes } => (*shape, lanes),
        };
        let Some(arity) = transport.interners().tuple_arity(shape) else {
            return Err(DispatchStop::broken(format!(
                "backend type test cannot read lane-form {shape:?}"
            )));
        };
        let shapes = match predicate.tuple_positions(arity) {
            TuplePositions::Never => return Ok(false),
            TuplePositions::Always => return Ok(true),
            TuplePositions::AnyOf(shapes) => shapes,
        };
        let views = transport_field_views(transport, shape, lanes).map_err(DispatchStop::broken)?;
        for shape in shapes {
            let mut matched = true;
            for (position, view) in shape.iter().zip(&views) {
                if !self.type_matches(position, view)? {
                    matched = false;
                    break;
                }
            }
            if matched {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Whether one whole runtime value satisfies a test.
    ///
    /// The partner of the decomposition above: where a lane-form subject is
    /// asked one question per position, a value that exists as one word is
    /// offered whole to the shared matcher.
    fn whole_value_matches(&mut self, predicate: &RuntimeTypePredicate, value: AnyValue) -> bool {
        let proc = self.proc();
        let Ok(runtime_value) = value.value(proc) else {
            return false;
        };
        let module = self.module;
        let (tuple_schema_ids, named_schema_ids) =
            interp_runtime_type_predicate_schema_ids(self.runtime, module, predicate);
        // The representation's owner answers what only it can: which callable a
        // code word denotes, and what a tuple's field holds.
        let (types, transport, program) = (self.types, self.operands.transport, self.program);
        let callables = |code: u64| backend_callable_identity(types, transport, program, code);
        let fields = |value: RuntimeAnyValue, index: usize| {
            let field = fz_struct_get_field_ref(proc, value.ref_word().raw_word(), (index as u32) * 8);
            interp_value_from_ref_word(field, "tuple shape field")
                .ok()
                .and_then(|value| value.value(proc).ok())
        };
        let list_head = |value: RuntimeAnyValue| {
            let head = fz_list_head_ref(value.ref_word().raw_word());
            interp_value_from_ref_word(head, "list head")
                .ok()
                .and_then(|value| value.value(proc).ok())
        };
        let list_tail = |value: RuntimeAnyValue| {
            let tail = fz_list_tail_ref(value.ref_word().raw_word());
            interp_value_from_ref_word(tail, "list tail")
                .ok()
                .and_then(|value| value.value(proc).ok())
        };
        let reader = RuntimeValueReader {
            module,
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            callables: &callables,
            fields: &fields,
            list_head: &list_head,
            list_tail: &list_tail,
        };
        let matched = matches_runtime_type_predicate(predicate, &reader, runtime_value);
        if matched {
            surface_membership::observe(predicate, &reader, runtime_value);
        }
        matched
    }

    fn eval_guard(&mut self, expr: &PatternGuardExpr<Ty>) -> Result<AnyValue, DispatchStop> {
        Ok(match expr {
            PatternGuardExpr::Const(c) => required(dispatch_const_to_value(self.proc(), self.module, c))?,
            PatternGuardExpr::Subject(subject) => self.subject_word(*subject)?,
            PatternGuardExpr::Pinned(pinned_id) => required(self.pin_value(*pinned_id))?,
            PatternGuardExpr::Unary { op, expr } => {
                let v = self.eval_guard(expr)?;
                match op {
                    PatternGuardUnaryOp::Not => interp_bool_value(v.is_false() || v.is_nil()),
                    // The same negation an EXPRESSION gets. Forcing the operand
                    // to an integer here made `when -x > 0.0` silently fail its
                    // guard for a float and fall to the next clause, so `interp`
                    // answered a different clause than `run` and `build`.
                    PatternGuardUnaryOp::Neg => required(super::binop::eval_unop(crate::fz_ir::UnOp::Neg, v).ok())?,
                }
            }
            PatternGuardExpr::Binary { op, lhs, rhs } => {
                let l = self.eval_guard(lhs)?;
                let short = match op {
                    PatternGuardBinOp::And if l.is_false() || l.is_nil() => Some(interp_bool_value(false)),
                    PatternGuardBinOp::Or if !(l.is_false() || l.is_nil()) => Some(interp_bool_value(true)),
                    _ => None,
                };
                if let Some(v) = short {
                    return Ok(v);
                }
                let r = self.eval_guard(rhs)?;
                let proc = self.proc();
                match op {
                    PatternGuardBinOp::Add => AnyValue::Int(required(guard_int(l))? + required(guard_int(r))?),
                    PatternGuardBinOp::Sub => AnyValue::Int(required(guard_int(l))? - required(guard_int(r))?),
                    PatternGuardBinOp::Mul => AnyValue::Int(required(guard_int(l))? * required(guard_int(r))?),
                    PatternGuardBinOp::Div => AnyValue::Int(required(guard_int(l))? / required(guard_int(r))?),
                    PatternGuardBinOp::Rem => AnyValue::Int(required(guard_int(l))? % required(guard_int(r))?),
                    // A guard's `==` is the `==` OPERATOR, so it widens: `when a
                    // == b` with a = 1 and b = 1.0 is true. Pattern MATCHING
                    // stays strict; the IR names the two questions separately,
                    // so both doors can ask this one.
                    PatternGuardBinOp::Eq => interp_bool_value(required(interp_operator_eq(proc, l, r).ok())?),
                    PatternGuardBinOp::Neq => interp_bool_value(!required(interp_operator_eq(proc, l, r).ok())?),
                    // A guard orders its operands the same way the rest of the
                    // language does, through `fz_value_cmp_ref`. Comparing as
                    // integers could not see a float at all: `when a >= b` with
                    // a = 2 and b = 1.0 failed the conversion and fell through
                    // to the next clause instead of answering true.
                    PatternGuardBinOp::Lt => interp_bool_value(required(guard_cmp(proc, l, r))? < 0),
                    PatternGuardBinOp::LtEq => interp_bool_value(required(guard_cmp(proc, l, r))? <= 0),
                    PatternGuardBinOp::Gt => interp_bool_value(required(guard_cmp(proc, l, r))? > 0),
                    PatternGuardBinOp::GtEq => interp_bool_value(required(guard_cmp(proc, l, r))? >= 0),
                    PatternGuardBinOp::And | PatternGuardBinOp::Or => interp_bool_value(!(r.is_false() || r.is_nil())),
                }
            }
            PatternGuardExpr::Dispatch {
                inputs,
                prepared,
                dispatch,
            } => {
                let mut values = Vec::with_capacity(inputs.len());
                for input in inputs {
                    values.push(Some(BackendBoundValue::Runtime(self.eval_guard(input)?)));
                }
                // A helper's prepared keys are its caller's, named by position:
                // the source constructor lifted every child key into this
                // plan's operands, so the remap is a read, not a build.
                let helper_pinned = DispatchValues {
                    pinned: Vec::new(),
                    prepared: required(
                        prepared
                            .iter()
                            .map(|id| self.operands.pinned.prepared.get(id.0 as usize).copied())
                            .collect::<Option<Vec<_>>>(),
                    )?,
                };
                let helper = Dispatch::new(
                    self.runtime,
                    self.types,
                    self.program,
                    self.module,
                    &dispatch.plan,
                    DispatchOperands {
                        transport: self.operands.transport,
                        inputs: &values,
                        pinned: &helper_pinned,
                    },
                );
                // A helper that matches nothing answers no value, which is a
                // guard that does not hold.
                let mut decided = required(helper.run().map_err(DispatchStop::Broken)?)?;
                let body = required(dispatch.bodies.get(dispatch.plan.body_id(decided.outcome()) as usize))?;
                decided.eval_guard(body)?
            }
        })
    }

    /// The map value one constant key denotes, or `None` where the subject is no
    /// map or holds no such key.
    fn map_lookup(&self, map: AnyValue, key: &GroundValue) -> Option<AnyValue> {
        let proc = self.proc();
        if !map.value(proc).ok().is_some_and(is_map_value) {
            return None;
        }
        let key = self.const_key_value(key)?;
        let ref_word = with_value_ref(proc, map, "DispatchMapGet map", |map_ref| {
            with_value_ref(proc, key, "DispatchMapGet key", |key_ref| {
                fz_matcher_map_get_ref(proc, map_ref, key_ref)
            })
        })
        .ok()?
        .ok()?;
        let value = interp_value_from_ref_word(ref_word, "DispatchMapGet").ok()?;
        match value {
            AnyValue::Null => None,
            _ => Some(value),
        }
    }

    /// The runtime word a map pattern's constant key compares against. A binary
    /// key is materialised before the run and read out of the prepared values.
    fn const_key_value(&self, key: &GroundValue) -> Option<AnyValue> {
        use crate::ground_value::DispatchShape;
        match key
            .as_dispatch_shape()
            .expect("const_key_value only ever sees a dispatch-matrix const")
        {
            DispatchShape::Int(n) => Some(AnyValue::Int(n)),
            DispatchShape::Float(bits) => Some(AnyValue::Float(f64::from_bits(bits))),
            DispatchShape::Bool(value) => Some(interp_bool_value(value)),
            DispatchShape::Nil => Some(interp_nil_value()),
            DispatchShape::Atom(name) => self
                .module
                .atom_names
                .iter()
                .position(|n| n == name)
                .map(|id| AnyValue::Atom(id as u32)),
            DispatchShape::Utf8Binary(_) => self
                .plan
                .prepared_key_id(key)
                .and_then(|id| self.operands.pinned.prepared.get(id.0 as usize).copied()),
        }
    }

    /// Read a bitstring subject field by field, binding what each field yields.
    fn read_bitstring(&mut self, value: RuntimeAnyValue, shape: &BitstringShape) -> bool {
        let Some(value_bits) = value.heap_object_word() else {
            return false;
        };
        let Some(p) = bitstring_like_ptr(value_bits) else {
            return false;
        };
        if !unsafe { is_bitstring_like(p) } {
            return false;
        }
        let plan = self.plan;
        let proc = self.proc();
        let mut reader = fz_bs_reader_init_ref(proc, value.ref_word().raw_word());
        for field_subject in &shape.fields {
            let extraction = plan.bitstring_extraction(*field_subject);
            let field = &extraction.spec;
            let Some((size_present, size_value)) = self.bit_size_value(&field.size) else {
                return false;
            };
            let Ok(reader_any) = interp_value_from_ref_word(reader, "bitstring dispatch reader") else {
                return false;
            };
            let Ok(reader_ref) = reader_any.as_ref_word(proc) else {
                return false;
            };
            let field_spec = fz_bs_field_spec(
                dispatch_bit_type_tag(field.kind),
                size_present,
                field.unit.unwrap_or(default_dispatch_bit_unit(field.kind)),
                dispatch_endian_tag(field.endian),
                field.signed as u32,
                extraction.is_last as u32,
            );
            let result = fz_bs_read_field_ref(proc, reader_ref, field_spec, size_value);
            let Ok(ok) = interp_struct_field_from_tagged_bits(proc, result, 0, "bitstring dispatch ok") else {
                return false;
            };
            if ok.is_false() || ok.is_nil() {
                return false;
            }
            let Ok(extracted) = interp_struct_field_from_tagged_bits(proc, result, 8, "bitstring dispatch extracted")
            else {
                return false;
            };
            let Ok(next_reader) =
                interp_struct_field_from_tagged_bits(proc, result, 16, "bitstring dispatch next reader")
            else {
                return false;
            };
            self.state
                .values
                .insert(*field_subject, BackendBoundValue::Runtime(extracted));
            let Ok(next_reader_ref) = next_reader.as_ref_word(proc) else {
                return false;
            };
            reader = next_reader_ref;
        }
        if !shape.require_done {
            return true;
        }
        let Ok(bit_len) = interp_struct_field_from_tagged_bits(proc, reader, 8, "bitstring dispatch bit_len") else {
            return false;
        };
        let Ok(pos) = interp_struct_field_from_tagged_bits(proc, reader, 16, "bitstring dispatch pos") else {
            return false;
        };
        bit_len.as_i64() == pos.as_i64()
    }

    /// How wide one bitstring field is, and whether it says so at all.
    fn bit_size_value(&self, size: &Option<BitstringFieldSize>) -> Option<(u32, u32)> {
        match size {
            None => Some((0, 0)),
            Some(BitstringFieldSize::Literal(n)) => Some((1, *n)),
            Some(BitstringFieldSize::Binding(subject)) => self
                .state
                .values
                .get(subject)
                .and_then(BackendBoundValue::runtime_word)
                .and_then(|v| v.as_i64())
                .map(|n| (1, n as u32)),
            // A size bound BEFORE THE PATTERN BEGAN, never a parameter of the
            // same head. It arrives as a PIN, which is the same mechanism
            // `Pattern::Pinned` uses, because it is the same question: a name
            // the pattern USES but does not BIND.
            Some(BitstringFieldSize::Pinned(pin_id)) => self
                .pin_value(*pin_id)
                .and_then(|value| value.as_i64())
                .map(|n| (1, n as u32)),
        }
    }

    /// The runtime word one pin was bound to before this pattern began.
    fn pin_value(&self, pinned: PinnedValueId) -> Option<AnyValue> {
        self.operands.pinned.pinned.get(pinned.0 as usize).copied()
    }

    fn proc(&self) -> *mut Process {
        self.runtime.cur_proc()
    }
}

/// A plan that has been decided, and the run that decided it.
///
/// A winning outcome's arguments are subjects that run produced, or can still
/// produce from the operands it holds, so they are read here and nowhere else:
/// there is no way to ask a run that never decided what it bound.
pub(super) struct Decided<'a> {
    run: Dispatch<'a>,
    outcome: OutcomeId,
}

impl Decided<'_> {
    pub(super) fn outcome(&self) -> OutcomeId {
        self.outcome
    }

    /// The one runtime word one of the winning outcome's arguments denotes.
    pub(super) fn subject_word(&mut self, subject: SubjectId) -> Result<AnyValue, DispatchStop> {
        self.run.subject_word(subject)
    }

    /// The value a guard body answers, decided against the same run.
    fn eval_guard(&mut self, expr: &PatternGuardExpr<Ty>) -> Result<AnyValue, DispatchStop> {
        self.run.eval_guard(expr)
    }
}

/// The i-th field of a lane-form tuple, as a view over lanes already in hand.
///
/// `None` where the subject is not a lane-form tuple, which is the signal to
/// read the field out of a runtime value instead. Only that field's own lanes
/// are read: a dispatch asks about one position at a time.
fn transport_tuple_field(
    transport: &TransportStore,
    value: &BackendBoundValue,
    index: usize,
) -> Result<Option<BackendBoundValue>, DispatchStop> {
    let BackendBoundValue::Transport { shape, lanes } = value else {
        return Ok(None);
    };
    if transport.interners().tuple_arity(*shape).is_none() {
        return Ok(None);
    }
    transport_field_view(transport, *shape, lanes, index)
        .map_err(DispatchStop::broken)?
        .map(Some)
        .ok_or_else(|| DispatchStop::broken(format!("dispatch tuple field {index} is out of bounds for {shape:?}")))
}

/// One dynamic ordering, shared with native codegen and with the `Kernel`
/// operators, so a guard cannot answer a comparison differently from the
/// expression that spells it out.
fn guard_cmp(proc: *mut Process, left: AnyValue, right: AnyValue) -> Option<i64> {
    interp_cmp(proc, left, right).ok()
}

pub(super) fn dispatch_const_to_value(proc: *mut Process, module: &Module, c: &GroundValue) -> Option<AnyValue> {
    use crate::ground_value::DispatchShape;
    match c
        .as_dispatch_shape()
        .expect("dispatch_const_to_value only ever sees a dispatch-matrix const")
    {
        DispatchShape::Int(n) => Some(AnyValue::Int(n)),
        DispatchShape::Float(bits) => Some(AnyValue::Float(f64::from_bits(bits))),
        DispatchShape::Atom(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| AnyValue::Atom(id as u32)),
        DispatchShape::Bool(value) => Some(interp_bool_value(value)),
        DispatchShape::Nil => Some(interp_nil_value()),
        DispatchShape::Utf8Binary(bytes) => utf8_binary_const_value(proc, bytes),
    }
}

fn utf8_binary_const_value(proc: *mut Process, bytes: &[u8]) -> Option<AnyValue> {
    fz_bs_begin(proc);
    for byte in bytes {
        fz_bs_write_field_ref(
            proc,
            AnyValue::Int(i64::from(*byte)).as_ref_word(proc).ok()?,
            dispatch_bit_type_tag(BitstringFieldKind::Integer),
            1,
            8,
            1,
            dispatch_endian_tag(BitstringEndian::Big),
            0,
        );
    }
    interp_value_from_ref_word(fz_bs_finalize(proc), "dispatch utf8 guard literal").ok()
}

fn dispatch_const_eq(proc: *mut Process, module: &Module, val: AnyValue, value: &GroundValue) -> bool {
    use crate::ground_value::DispatchShape;
    match value
        .as_dispatch_shape()
        .expect("dispatch_const_eq only ever sees a dispatch-matrix const")
    {
        DispatchShape::Int(n) => val.as_i64() == Some(n),
        DispatchShape::Float(bits) => {
            matches!(val, AnyValue::Float(f) if f.to_bits() == bits)
        }
        DispatchShape::Atom(name) => module
            .atom_names
            .iter()
            .position(|n| n == name)
            .is_some_and(|id| val.is_atom_id(id as u32)),
        DispatchShape::Bool(true) => val.is_atom_id(TRUE_ATOM_ID),
        DispatchShape::Bool(false) => val.is_false(),
        DispatchShape::Nil => val.is_nil(),
        DispatchShape::Utf8Binary(bytes) => match val {
            AnyValue::FnRef(..) => false,
            other => other.value(proc).ok().is_some_and(|val| {
                val.heap_object_word().and_then(bitstring_like_ptr).is_some_and(|p| {
                    if !unsafe { is_bitstring_like(p) } {
                        return false;
                    }
                    let bit_len = unsafe { bitstring_bit_len(p) };
                    if bit_len != (bytes.len() as u64) * 8 {
                        return false;
                    }
                    let ptr = unsafe { bitstring_byte_ptr(p) };
                    let slice = unsafe { from_raw_parts(ptr, bytes.len()) };
                    slice == bytes
                })
            }),
        },
    }
}

fn dispatch_bit_type_tag(ty: BitstringFieldKind) -> u32 {
    match ty {
        BitstringFieldKind::Integer => 0,
        BitstringFieldKind::Float => 1,
        BitstringFieldKind::Binary => 2,
        BitstringFieldKind::Bits => 3,
        BitstringFieldKind::Utf8 => 4,
        BitstringFieldKind::Utf16 => 5,
        BitstringFieldKind::Utf32 => 6,
    }
}

fn dispatch_endian_tag(endian: BitstringEndian) -> u32 {
    match endian {
        BitstringEndian::Big => 0,
        BitstringEndian::Little => 1,
        BitstringEndian::Native => 2,
    }
}

fn default_dispatch_bit_unit(ty: BitstringFieldKind) -> u32 {
    match ty {
        BitstringFieldKind::Integer | BitstringFieldKind::Float | BitstringFieldKind::Bits => 1,
        BitstringFieldKind::Binary => 8,
        BitstringFieldKind::Utf8 | BitstringFieldKind::Utf16 | BitstringFieldKind::Utf32 => 1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Pattern, Spanned};
    use crate::compiler2::World;
    use crate::compiler2::transport::{ShapeDescr, TransportLayout};
    use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};

    fn one_input_plan(patterns: Vec<Pattern>) -> PatternDispatchPlan<Ty> {
        pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            patterns
                .into_iter()
                .enumerate()
                .map(|(body_id, pattern)| PatternRow {
                    patterns: vec![Spanned::dummy(pattern)],
                    preconditions: Vec::new(),
                    guard: None,
                    body_id: body_id as u32,
                })
                .collect(),
        ))
        .expect("a one-input head compiles")
    }

    /// An entry head whose captures arrive as leading inputs, pinning the one
    /// that delivers `want`.
    fn entry_plan_pinning_input_zero() -> PatternDispatchPlan<Ty> {
        pattern_dispatch_from_source(SourcePatternRows::entry(
            2,
            vec![PatternRow {
                patterns: vec![
                    Spanned::dummy(Pattern::Wildcard),
                    Spanned::dummy(Pattern::Pinned("want".to_string())),
                ],
                preconditions: Vec::new(),
                guard: None,
                body_id: 0,
            }],
            vec![("want".to_string(), 0)],
        ))
        .expect("an entry head that pins a delivered input compiles")
    }

    fn live_runtime() -> IrInterpRuntime {
        let mut runtime = IrInterpRuntime::fresh_with_atoms(Vec::new());
        runtime.current_proc = runtime.process_ptr(1).unwrap();
        runtime
    }

    /// An input the plan reads that never arrived is a disagreement between the
    /// plan and its caller, not a subject that simply failed its test.
    #[test]
    fn an_input_the_plan_reads_but_never_received_stops_the_run() {
        let plan = one_input_plan(vec![Pattern::Tuple(vec![Spanned::dummy(Pattern::Wildcard)])]);
        let mut runtime = live_runtime();
        let world = World::new();
        let program = crate::compiler2::BackendProgram::empty_for_test();
        let transport = TransportStore::new();
        let pinned = DispatchValues::default();
        let module = Module::default();
        let error = Dispatch::new(
            &mut runtime,
            world.types(),
            &program,
            &module,
            &plan,
            DispatchOperands {
                transport: &transport,
                inputs: &[],
                pinned: &pinned,
            },
        )
        .run()
        .err()
        .expect("the plan reads the only input, which was never delivered");
        assert_eq!(error, "dispatch reads input 0, which did not arrive");
    }

    /// The door answers which clause of a multi-clause plan the operands chose.
    #[test]
    fn the_door_decides_which_clause_the_operands_choose() {
        let plan = one_input_plan(vec![Pattern::Int(1), Pattern::Var("other".to_string())]);
        let mut runtime = live_runtime();
        let world = World::new();
        let program = crate::compiler2::BackendProgram::empty_for_test();
        let transport = TransportStore::new();
        let pinned = DispatchValues::default();
        let module = Module::default();
        for (input, expected_body) in [(1, 0u32), (2, 1)] {
            let inputs = [Some(BackendBoundValue::Runtime(AnyValue::Int(input)))];
            let decided = Dispatch::new(
                &mut runtime,
                world.types(),
                &program,
                &module,
                &plan,
                DispatchOperands {
                    transport: &transport,
                    inputs: &inputs,
                    pinned: &pinned,
                },
            )
            .run()
            .expect("the plan decides")
            .expect("a clause matched");
            assert_eq!(
                plan.body_id(decided.outcome()),
                expected_body,
                "the door answers the clause the operands chose"
            );
        }
    }

    /// The outcome's arguments are read off the decision itself: the bindings a
    /// winning clause carries name subjects, and the run that decided produces
    /// them from the operands it already holds.
    #[test]
    fn an_outcome_argument_reads_the_run_that_decided_it() {
        let plan = one_input_plan(vec![Pattern::Int(1), Pattern::Var("other".to_string())]);
        let mut runtime = live_runtime();
        let world = World::new();
        let program = crate::compiler2::BackendProgram::empty_for_test();
        let transport = TransportStore::new();
        let pinned = DispatchValues::default();
        let module = Module::default();
        let inputs = [Some(BackendBoundValue::Runtime(AnyValue::Int(7)))];
        let mut decided = Dispatch::new(
            &mut runtime,
            world.types(),
            &program,
            &module,
            &plan,
            DispatchOperands {
                transport: &transport,
                inputs: &inputs,
                pinned: &pinned,
            },
        )
        .run()
        .expect("the plan decides")
        .expect("a clause matched");
        let binding = plan
            .outcome(decided.outcome())
            .expect("a winning outcome")
            .bindings
            .first()
            .expect("the matching clause binds its variable")
            .clone();
        let bound = decided
            .subject_word(binding.source)
            .expect("the decision holds the subject");
        assert_eq!(
            bound.as_i64(),
            Some(7),
            "the winning outcome's argument comes from the operands the run decided on"
        );
    }

    /// One pin, two doors: an entry plan reads it out of the input that
    /// delivered it and a match site reads it out of its environment, through
    /// the same operand builder.
    #[test]
    fn a_pin_comes_from_an_input_ordinal_or_from_an_environment_value() {
        let entry_plan = entry_plan_pinning_input_zero();
        let site_plan = one_input_plan(vec![Pattern::Pinned("want".to_string())]);
        let runtime = live_runtime();
        let transport = TransportStore::new();
        let module = Module::default();
        let want = AnyValue::Int(41);

        let inputs = [Some(BackendBoundValue::Runtime(want)), None];
        let from_input = dispatch_values(
            runtime.cur_proc(),
            &transport,
            &module,
            &entry_plan,
            DispatchSource::Inputs(&inputs),
        )
        .expect("the delivering input supplies the pin");

        let value = ValueId::from_u32(3);
        let env = HashMap::from([(value, BackendBoundValue::Runtime(want))]);
        let bindings = DispatchBindings {
            pinned: vec![value],
            prepared: Vec::new(),
        };
        let from_env = dispatch_values(
            runtime.cur_proc(),
            &transport,
            &module,
            &site_plan,
            DispatchSource::Bound {
                env: &env,
                bindings: &bindings,
            },
        )
        .expect("the named environment value supplies the pin");

        assert_eq!(
            from_input.pinned.len(),
            1,
            "an entry plan's pin is one operand beyond its inputs"
        );
        assert_eq!(
            from_input.pinned[0].as_i64(),
            from_env.pinned[0].as_i64(),
            "both doors hand the executor the same pinned word"
        );
    }

    /// A pin is compared whole, so a delivering input that arrived as lanes
    /// carries no operand for it, and the refusal names the pin.
    #[test]
    fn a_pin_whose_input_arrives_in_lane_form_is_refused_by_name() {
        let plan = entry_plan_pinning_input_zero();
        let runtime = live_runtime();
        let mut transport = TransportStore::new();
        let nothing = transport.interners_mut().intern_shape(ShapeDescr::Nothing);
        let tuple = transport
            .interners_mut()
            .intern_shape(ShapeDescr::Tuple(Box::from([TransportLayout::structural(nothing)])));
        let inputs = [
            Some(BackendBoundValue::Transport {
                shape: tuple,
                lanes: Vec::new(),
            }),
            None,
        ];
        let error = dispatch_values(
            runtime.cur_proc(),
            &transport,
            &Module::default(),
            &plan,
            DispatchSource::Inputs(&inputs),
        )
        .expect_err("a lane-form input holds no single word to compare against");
        assert_eq!(error, "dispatch pin `want` has no runtime argument operand");
    }
}
