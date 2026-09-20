//! What a function returns, and what it hands each of its callees, written
//! before any activation exists.
//!
//! A *skeleton* is the shape of a value in one function's own vocabulary:
//! its input slots and the results of its own call sites. It is the
//! companion an activation's walk carries, minus the specialization -- the
//! walk's `ReturnExpression` is this same tree with `Input{slot}` bound to
//! the type that arrived and `Result(callsite)` bound to the activation the
//! call reached.
//!
//! Two skeletons are published per function: the one its return is built
//! from, and one per argument of each call site. Together with the static
//! call graph they close: a call site's argument skeleton feeds the callee's
//! slot, and the callee's return skeleton feeds the call site's result. That
//! closure is what `return_unknowns` walks to decide, statically, which
//! positions a fixpoint is still solving -- an answer keying needs in its
//! first round, before any evidence exists to read.
//!
//! The lowering is structural and total: every step whose result has a shape
//! the analysis can name (a constructor, a projection) contributes that
//! shape, and every other step contributes `Ground` -- a value the fixpoint
//! never has to solve for, because arithmetic, a bitstring read or a lambda
//! denotes what it denotes whatever its operands are still climbing towards.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::dispatch_matrix::ProjectionKind;
use crate::ground_value::GroundValue;

use super::body::{
    CallInputMode, CallSiteId, ControlDestination, ControlEntryId, DeliveredValueSource, LoweredBody, LoweredStep,
    LoweredTail, SubjectOriginRoot, ValueId, delivered_value_joins,
};
use super::identity::FunctionId;
use super::semantic::ProjectStep;
use super::types::MapKey;

/// One value's shape in its own function's vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub(crate) enum Skeleton {
    /// A value whose denotation owes nothing to a position being solved.
    #[default]
    Ground,
    /// The function's `slot`th semantic input.
    Input(usize),
    /// What one of this function's own call sites yields.
    Result(CallSiteId),
    /// The join of several paths: a branch, a dispatch, a delivered resume.
    Union(Vec<Skeleton>),
    Tuple(Vec<Skeleton>),
    /// A list, by its uniform element. Emptiness is a property of the value
    /// that arrives, never of the shape: both list constructors guard their
    /// element the same way, so one form carries both.
    List(Box<Skeleton>),
    /// A map or a struct, by its literal-keyed fields. A struct is a map
    /// whose keys are its field atoms, so it needs no form of its own.
    Map(Vec<(MapKey, Skeleton)>),
    /// One layer read back out of a value whose own shape is still symbolic.
    /// Built only by [`Skeleton::project`], which reduces the read away
    /// wherever the subject already carries the matching constructor.
    Project {
        of: Box<Skeleton>,
        step: ProjectStep,
    },
}

impl Skeleton {
    /// Read one layer out of `of`, reducing structurally wherever `of`
    /// already carries the constructor being read -- the same reduction
    /// `ReturnExpression::project` performs, with no `Types` to consult
    /// because a `Ground` value answers for itself.
    pub(crate) fn project(of: Skeleton, step: ProjectStep) -> Skeleton {
        match (&of, &step) {
            // A ground value has no layers to read.
            (Skeleton::Ground, _) => Skeleton::Ground,
            (Skeleton::Union(branches), _) => branches
                .clone()
                .into_iter()
                .map(|branch| Skeleton::project(branch, step.clone()))
                .fold(Skeleton::Ground, Skeleton::union),
            (Skeleton::Tuple(elems), ProjectStep::TupleField(index)) => {
                elems.get(*index).cloned().unwrap_or(Skeleton::Ground)
            }
            (Skeleton::List(elem), ProjectStep::ListElement) => (**elem).clone(),
            (Skeleton::List(_), ProjectStep::ListTail) => of.clone(),
            (Skeleton::Map(fields), ProjectStep::MapField(wanted)) => fields
                .iter()
                .find(|(key, _)| key == wanted)
                .map(|(_, value)| value.clone())
                .unwrap_or(Skeleton::Ground),
            _ => Skeleton::Project { of: Box::new(of), step },
        }
    }

    /// Join two paths. `Ground` is the identity: a path that owes nothing to
    /// a position being solved constrains nothing about where the others
    /// still are, so it adds no alternative anyone has to carry. That makes
    /// it the fold's seed as well as its neutral branch, and a join of
    /// nothing but settled paths is itself settled.
    pub(crate) fn union(a: Skeleton, b: Skeleton) -> Skeleton {
        match (a, b) {
            (Skeleton::Ground, other) | (other, Skeleton::Ground) => other,
            (Skeleton::Union(mut members), Skeleton::Union(more)) => {
                members.extend(more);
                Skeleton::Union(members)
            }
            (Skeleton::Union(mut members), x) => {
                members.push(x);
                Skeleton::Union(members)
            }
            (x, Skeleton::Union(mut members)) => {
                members.insert(0, x);
                Skeleton::Union(members)
            }
            (x, y) => Skeleton::Union(vec![x, y]),
        }
    }
}

/// One function's whole static shape: what it returns and what each of its
/// call sites passes, all in that function's own vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct FunctionSkeleton {
    pub(crate) returns: Skeleton,
    /// One entry per call site, holding that site's positional arguments.
    pub(crate) arguments: BTreeMap<CallSiteId, Vec<Skeleton>>,
    /// The function a call site names in the body itself.
    pub(crate) callees: BTreeMap<CallSiteId, (FunctionId, CallInputMode)>,
    /// How many semantic inputs the function has, which is what a call
    /// site's positional arguments are mapped onto.
    pub(crate) input_len: usize,
}

/// Lowers one body to its skeleton.
///
/// The scan is flat over clauses and entries, which visits exactly the
/// callsites and steps a recursive walk of the control links would (see
/// `body::callsite_input_modes` for the invariant that makes it sound), and
/// values are resolved on demand from that map, so a value defined after its
/// use in the arena is still resolved from its own definition.
pub(crate) fn lower(body: &LoweredBody) -> FunctionSkeleton {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return FunctionSkeleton::default();
    };
    let mut lowering = Lowering {
        body,
        definitions: HashMap::new(),
        memo: HashMap::new(),
        visiting: HashSet::new(),
    };
    for clause in clauses {
        for (slot, value) in clause.params.iter().copied().enumerate() {
            lowering.definitions.insert(value, Definition::Input(slot));
        }
        for step in &clause.projections {
            lowering.record_step(step);
        }
    }
    for (index, entry) in entries.iter().enumerate() {
        let owner = ControlEntryId::from_u32(index as u32);
        for step in &entry.steps {
            lowering.record_step(step);
        }
        for edge in entry.tail.outcome_edges() {
            for argument in &edge.arguments {
                lowering
                    .definitions
                    .insert(argument.parameter, Definition::Subject(owner, argument.subject));
            }
        }
        if let LoweredTail::DirectCall { value, callsite, .. } | LoweredTail::ClosureCall { value, callsite, .. } =
            &entry.tail
        {
            lowering.definitions.insert(*value, Definition::Result(*callsite));
        }
    }
    for join in delivered_value_joins(body).into_values() {
        lowering.definitions.insert(
            join.value,
            Definition::Delivered(
                join.sources
                    .iter()
                    .map(|source| match source {
                        DeliveredValueSource::LocalValue(value) => Definition::Alias(*value),
                        DeliveredValueSource::CallsiteReturn(callsite) => Definition::Result(*callsite),
                    })
                    .collect(),
            ),
        );
    }

    let mut returns = Skeleton::Ground;
    let mut arguments = BTreeMap::new();
    let mut callees = BTreeMap::new();
    for entry in entries {
        match &entry.tail {
            LoweredTail::Value {
                value,
                dest: ControlDestination::Return,
            } => {
                let contribution = lowering.resolve(*value);
                returns = Skeleton::union(returns, contribution);
            }
            LoweredTail::DirectCall {
                callsite,
                callee,
                args,
                dest,
                ..
            } => {
                callees.insert(*callsite, (*callee, CallInputMode::Direct));
                arguments.insert(
                    *callsite,
                    args.iter().map(|arg| lowering.resolve(arg.value)).collect::<Vec<_>>(),
                );
                if matches!(dest, ControlDestination::Return) {
                    returns = Skeleton::union(returns, Skeleton::Result(*callsite));
                }
            }
            LoweredTail::ClosureCall {
                callsite, args, dest, ..
            } => {
                arguments.insert(
                    *callsite,
                    args.iter().map(|arg| lowering.resolve(arg.value)).collect::<Vec<_>>(),
                );
                if matches!(dest, ControlDestination::Return) {
                    returns = Skeleton::union(returns, Skeleton::Result(*callsite));
                }
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Halt { .. } => {}
        }
    }
    FunctionSkeleton {
        returns,
        arguments,
        callees,
        input_len: clauses.first().map_or(0, |clause| clause.params.len()),
    }
}

/// How one value comes to be, before its operands are resolved.
#[derive(Debug, Clone)]
enum Definition {
    Input(usize),
    Result(CallSiteId),
    Alias(ValueId),
    Subject(ControlEntryId, crate::dispatch_matrix::SubjectId),
    Delivered(Vec<Definition>),
    Tuple(Vec<ValueId>),
    /// A list by its element sources: the items, and the tail whose own
    /// elements join them.
    List {
        items: Vec<ValueId>,
        tail: Option<ValueId>,
    },
    Map(Vec<(MapKey, ValueId)>),
    Project(ValueId, ProjectStep),
}

struct Lowering<'a> {
    body: &'a LoweredBody,
    definitions: HashMap<ValueId, Definition>,
    memo: HashMap<ValueId, Skeleton>,
    visiting: HashSet<ValueId>,
}

impl Lowering<'_> {
    fn record_step(&mut self, step: &LoweredStep) {
        let definition = match step {
            LoweredStep::Tuple { value, items } => {
                (*value, Definition::Tuple(items.iter().map(|item| item.value).collect()))
            }
            LoweredStep::List { value, items, tail, .. } => (
                *value,
                Definition::List {
                    items: items.clone(),
                    tail: *tail,
                },
            ),
            LoweredStep::Map { value, entries, .. } => match map_fields(entries) {
                Some(fields) => (*value, Definition::Map(fields)),
                None => return,
            },
            LoweredStep::Struct { value, fields, .. } => (
                *value,
                Definition::Map(
                    fields
                        .iter()
                        .map(|(name, field)| (MapKey::Atom(name.clone()), *field))
                        .collect(),
                ),
            ),
            LoweredStep::MapIndex { value, base, key } => match key.literal.as_ref().and_then(map_key) {
                Some(key) => (*value, Definition::Project(*base, ProjectStep::MapField(key))),
                None => return,
            },
            LoweredStep::FieldAccess { value, base, field } => (
                *value,
                Definition::Project(*base, ProjectStep::MapField(MapKey::Atom(field.clone()))),
            ),
            LoweredStep::RequireMapValue { value, source, key } => match map_key(key) {
                Some(key) => (*value, Definition::Project(*source, ProjectStep::MapField(key))),
                None => return,
            },
            LoweredStep::TupleField { value, source, index } => {
                (*value, Definition::Project(*source, ProjectStep::TupleField(*index)))
            }
            LoweredStep::AssertSame { source, value } => (*value, Definition::Alias(*source)),
            LoweredStep::SplitList { source, head, tail } => {
                self.definitions
                    .insert(*head, Definition::Project(*source, ProjectStep::ListElement));
                (*tail, Definition::Project(*source, ProjectStep::ListTail))
            }
            // A value with no shape of its own: it denotes what it denotes
            // whatever its operands are still climbing towards.
            LoweredStep::Const { .. }
            | LoweredStep::FunctionRef { .. }
            | LoweredStep::Lambda { .. }
            | LoweredStep::MapUpdate { .. }
            | LoweredStep::Bitstring { .. }
            | LoweredStep::BinaryOp { .. }
            | LoweredStep::UnaryOp { .. }
            | LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertStruct { .. }
            | LoweredStep::AssertTuple { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::BitstringInit { .. }
            | LoweredStep::BitstringRead { .. }
            | LoweredStep::AssertBitstringDone { .. } => return,
        };
        self.definitions.insert(definition.0, definition.1);
    }

    fn resolve(&mut self, value: ValueId) -> Skeleton {
        if let Some(known) = self.memo.get(&value) {
            return known.clone();
        }
        if !self.visiting.insert(value) {
            // A value can only reach itself through a delivered join that a
            // later entry feeds; the turn itself carries no shape.
            return Skeleton::Ground;
        }
        let definition = self.definitions.get(&value).cloned();
        let skeleton = match definition {
            None => Skeleton::Ground,
            Some(definition) => self.resolve_definition(&definition),
        };
        self.visiting.remove(&value);
        self.memo.insert(value, skeleton.clone());
        skeleton
    }

    fn resolve_definition(&mut self, definition: &Definition) -> Skeleton {
        match definition {
            Definition::Input(slot) => Skeleton::Input(*slot),
            Definition::Result(callsite) => Skeleton::Result(*callsite),
            Definition::Alias(source) => self.resolve(*source),
            Definition::Subject(owner, subject) => self.resolve_subject(*owner, *subject),
            Definition::Delivered(sources) => sources
                .iter()
                .map(|source| self.resolve_definition(&source.clone()))
                .fold(Skeleton::Ground, Skeleton::union),
            Definition::Tuple(items) => Skeleton::Tuple(items.iter().copied().map(|item| self.resolve(item)).collect()),
            Definition::List { items, tail } => {
                let mut element = items
                    .iter()
                    .copied()
                    .map(|item| self.resolve(item))
                    .fold(Skeleton::Ground, Skeleton::union);
                if let Some(tail) = tail {
                    let tail_element = Skeleton::project(self.resolve(*tail), ProjectStep::ListElement);
                    element = Skeleton::union(element, tail_element);
                }
                Skeleton::List(Box::new(element))
            }
            Definition::Map(fields) => Skeleton::Map(
                fields
                    .iter()
                    .map(|(key, value)| (key.clone(), self.resolve(*value)))
                    .collect(),
            ),
            Definition::Project(source, step) => {
                let of = self.resolve(*source);
                Skeleton::project(of, step.clone())
            }
        }
    }

    /// A dispatch outcome binds an entry parameter to a projection path out
    /// of one of the dispatch's own inputs. The path is the same one the
    /// walk reads, so the skeleton reads it with the same steps.
    fn resolve_subject(&mut self, owner: ControlEntryId, subject: crate::dispatch_matrix::SubjectId) -> Skeleton {
        let (root, path) = self.body.dispatch_subject_origin(owner, subject);
        let SubjectOriginRoot::Value(value) = root else {
            return Skeleton::Ground;
        };
        let mut skeleton = self.resolve(value);
        for kind in path {
            let Some(step) = projection_step(kind) else {
                return Skeleton::Ground;
            };
            skeleton = Skeleton::project(skeleton, step);
        }
        skeleton
    }
}

fn map_fields(entries: &[(super::body::LoweredMapKey, ValueId)]) -> Option<Vec<(MapKey, ValueId)>> {
    entries
        .iter()
        .map(|(key, value)| Some((map_key(key.literal.as_ref()?)?, *value)))
        .collect()
}

fn map_key(literal: &GroundValue) -> Option<MapKey> {
    match literal {
        GroundValue::Atom(name) => Some(MapKey::Atom(name.clone())),
        GroundValue::Int(value) => Some(MapKey::Int(*value)),
        _ => None,
    }
}

fn projection_step(kind: &ProjectionKind) -> Option<ProjectStep> {
    match kind {
        ProjectionKind::TupleField(index) => Some(ProjectStep::TupleField(*index as usize)),
        ProjectionKind::StructField(name) => Some(ProjectStep::MapField(MapKey::Atom(name.clone()))),
        ProjectionKind::ListHead => Some(ProjectStep::ListElement),
        ProjectionKind::ListTail => Some(ProjectStep::ListTail),
        ProjectionKind::MapValue { key } => map_key(key).map(ProjectStep::MapField),
        ProjectionKind::BitstringField(_) => None,
    }
}

#[cfg(test)]
#[path = "return_skeleton_test.rs"]
mod return_skeleton_test;
