//! What a function returns, and what it hands each of its callees, written
//! before any activation exists.
//!
//! A *skeleton* is the shape of a value in one function's own vocabulary:
//! its input slots, the results of its own call sites, and the values its
//! own steps produced. It is the ONE lowering of "what does this return".
//! The static readers (`return_unknowns`) read it as it stands; a solve
//! reads the same tree with each leaf bound to what one activation's walk
//! observed there -- a `Ground` value to its type, a `Result` to the
//! activations the call site reached.
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
//! shape, and every other step contributes the `Ground` value itself --
//! arithmetic, a bitstring read or a lambda denotes what it denotes whatever
//! its operands are still climbing towards, and an activation's own walk is
//! what says what that is.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::dispatch_matrix::ProjectionKind;
use crate::ground_value::GroundValue;

use super::body::{
    CallInputMode, CallSiteId, ControlDestination, ControlEntryId, DeliveredValueSource, LoweredBody, LoweredExtern,
    LoweredStep, LoweredTail, SubjectOriginRoot, ValueId, delivered_value_joins,
};
use super::identity::{FunctionId, ModuleId};
use super::semantic::ProjectStep;
use super::types::{MapKey, Ty, Types};

/// One value's shape in its own function's vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub(crate) enum Skeleton {
    /// No path reaches this position: the join identity, and what a read
    /// that the shape cannot promise leaves behind.
    #[default]
    Bottom,
    /// A value with no structural history of its own, named by the value
    /// that carries it. What it denotes is whatever the walk observed
    /// standing there; a walk that has observed nothing yet leaves it
    /// unbound, which is an unknown leaf and never `any` or `none`.
    Ground(ValueId),
    /// The function's `slot`th semantic input.
    Input(usize),
    /// What one of this function's own call sites yields. `value` is the
    /// value the call delivered into the body, which is what the shape
    /// denotes when the site addressed no activation at all -- a boundary
    /// edge, or a target nothing has resolved yet.
    Result {
        callsite: CallSiteId,
        value: ValueId,
    },
    /// The join of several paths: a branch, a dispatch, a delivered resume.
    Union(Vec<Skeleton>),
    Tuple(Vec<Skeleton>),
    /// A list, by its uniform element. `non_empty` records what the
    /// constructor itself proves: a literal with items and no tail holds at
    /// least one element whatever arrives, while a cons onto a tail inherits
    /// the tail's own emptiness.
    List {
        element: Box<Skeleton>,
        non_empty: bool,
    },
    /// A map by its literal-keyed fields.
    Map(Vec<(MapKey, Skeleton)>),
    /// A struct: a map whose keys are its field atoms, carrying the module
    /// that brands it so the brand survives into the solved type.
    Struct(ModuleId, Vec<(MapKey, Skeleton)>),
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
    /// already carries the constructor being read. A read a constructor
    /// cannot promise -- a tuple index past its arity -- reaches no value at
    /// all, so it is `Bottom`; a read of a leaf keeps the `Project` node,
    /// because what that leaf holds is an activation's answer, not a static
    /// one.
    pub(crate) fn project(of: Skeleton, step: ProjectStep) -> Skeleton {
        match (&of, &step) {
            (Skeleton::Bottom, _) => Skeleton::Bottom,
            (Skeleton::Union(branches), _) => branches
                .clone()
                .into_iter()
                .map(|branch| Skeleton::project(branch, step.clone()))
                .fold(Skeleton::Bottom, Skeleton::union),
            (Skeleton::Tuple(elems), ProjectStep::TupleField(index)) => {
                elems.get(*index).cloned().unwrap_or(Skeleton::Bottom)
            }
            (Skeleton::List { element, .. }, ProjectStep::ListElement) => (**element).clone(),
            // Removing one element leaves the same uniform shape behind, no
            // longer proven non-empty.
            (Skeleton::List { element, .. }, ProjectStep::ListTail) => Skeleton::List {
                element: element.clone(),
                non_empty: false,
            },
            (Skeleton::Map(fields) | Skeleton::Struct(_, fields), ProjectStep::MapField(wanted))
                if fields.iter().any(|(key, _)| key == wanted) =>
            {
                fields
                    .iter()
                    .find(|(key, _)| key == wanted)
                    .map(|(_, value)| value.clone())
                    .expect("the guard just proved this field is present")
            }
            _ => Skeleton::Project { of: Box::new(of), step },
        }
    }

    /// Join two paths. `Bottom` is the identity: a path that reaches no
    /// value adds no alternative anyone has to carry, which makes it the
    /// fold's seed as well as its neutral branch.
    ///
    /// A join is a SET operation, so it is idempotent: joining a skeleton
    /// with an alternative the flat list already holds is that list
    /// unchanged. Order is first occurrence first, so the result reads the
    /// way the lowering found it.
    pub(crate) fn union(a: Skeleton, b: Skeleton) -> Skeleton {
        let mut members = Vec::new();
        Skeleton::collect_union_member(&mut members, a);
        Skeleton::collect_union_member(&mut members, b);
        match members.len() {
            0 => Skeleton::Bottom,
            1 => members.pop().expect("a one-member join is that member"),
            _ => Skeleton::Union(members),
        }
    }

    fn collect_union_member(out: &mut Vec<Skeleton>, skeleton: Skeleton) {
        match skeleton {
            Skeleton::Bottom => {}
            Skeleton::Union(members) => members
                .into_iter()
                .for_each(|member| Skeleton::collect_union_member(out, member)),
            member => {
                if !out.contains(&member) {
                    out.push(member);
                }
            }
        }
    }

    /// Every value a return solve reads out of `Bindings::observed`, which is
    /// called at exactly two positions: every `Ground` leaf, and a `Result`
    /// leaf whose call site this walk left unaddressed -- no target it
    /// resolved to named an activation. An addressed `Result` leaf is instead
    /// answered by the component's equations (`Term::Return`), never by
    /// `value_types`, so its observed value is not in this set: including it
    /// would wake a solve on a value the solve does not read.
    fn collect_solved_leaves(&self, addressed: &HashSet<CallSiteId>, out: &mut HashSet<ValueId>) {
        match self {
            Skeleton::Bottom | Skeleton::Input(_) => {}
            Skeleton::Ground(value) => {
                out.insert(*value);
            }
            Skeleton::Result { callsite, value } => {
                if !addressed.contains(callsite) {
                    out.insert(*value);
                }
            }
            Skeleton::Union(branches) | Skeleton::Tuple(branches) => {
                for branch in branches {
                    branch.collect_solved_leaves(addressed, out);
                }
            }
            Skeleton::List { element, .. } => element.collect_solved_leaves(addressed, out),
            Skeleton::Map(fields) | Skeleton::Struct(_, fields) => {
                for (_, value) in fields {
                    value.collect_solved_leaves(addressed, out);
                }
            }
            Skeleton::Project { of, .. } => of.collect_solved_leaves(addressed, out),
        }
    }
}

/// What a function hands back.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Returns {
    /// An extern body has no entries to walk: the source states the return
    /// outright, and that statement is the whole answer.
    Declared(Ty),
    /// A provider boundary has no body in this compilation. Its return may
    /// depend on any value it is handed, but names no structural equation.
    Opaque,
    /// One shape per control entry that returns. WHICH of them a given
    /// activation reaches is a property of that activation, so the entries
    /// stay apart here and are joined against its `reachable_entries`.
    Entries(BTreeMap<ControlEntryId, Skeleton>),
}

impl Default for Returns {
    fn default() -> Self {
        Returns::Entries(BTreeMap::new())
    }
}

/// One function's whole static shape: what it returns and what each of its
/// call sites passes, all in that function's own vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct FunctionSkeleton {
    pub(crate) returns: Returns,
    /// One entry per call site, holding that site's positional arguments.
    pub(crate) arguments: BTreeMap<CallSiteId, Vec<Skeleton>>,
    /// The function a call site names in the body itself.
    pub(crate) callees: BTreeMap<CallSiteId, (FunctionId, CallInputMode)>,
    /// How many semantic inputs the function has, which is what a call
    /// site's positional arguments are mapped onto.
    pub(crate) input_len: usize,
}

impl FunctionSkeleton {
    /// The slice of an activation's `value_types` a return solve actually
    /// reads: the types standing at this function's `Ground` leaves and its
    /// unaddressed `Result` leaves, across both its return shapes and every
    /// call site's argument shapes. `addressed_callsites` is this walk's own
    /// answer to which call sites it resolved to an activation -- the same
    /// value it publishes as `CallSiteTargets` -- so a `Result` leaf whose
    /// call site the component's equations already answer is excluded here
    /// too. Everything else `value_types` carries is not a value the solve
    /// reads, so a solve subscribed to only this slice sees the same answer a
    /// whole-fact subscription would, without waking on the rest.
    pub(crate) fn return_solve_inputs(
        &self,
        value_types: &HashMap<ValueId, Ty>,
        addressed_callsites: &HashSet<CallSiteId>,
    ) -> HashMap<ValueId, Ty> {
        let mut leaves = HashSet::new();
        if let Returns::Entries(entries) = &self.returns {
            for shape in entries.values() {
                shape.collect_solved_leaves(addressed_callsites, &mut leaves);
            }
        }
        for shapes in self.arguments.values() {
            for shape in shapes {
                shape.collect_solved_leaves(addressed_callsites, &mut leaves);
            }
        }
        value_types
            .iter()
            .filter(|(value, _)| leaves.contains(value))
            .map(|(value, ty)| (*value, *ty))
            .collect()
    }
}

/// Lowers one body to its skeleton.
///
/// The scan is flat over clauses and entries, which visits exactly the
/// callsites and steps a recursive walk of the control links would (see
/// `body::callsite_input_modes` for the invariant that makes it sound), and
/// values are resolved on demand from that map, so a value defined after its
/// use in the arena is still resolved from its own definition.
pub(crate) fn lower(body: &LoweredBody, types: &Types) -> FunctionSkeleton {
    let (clauses, entries) = match body {
        LoweredBody::Extern { signature } => return extern_skeleton(signature, types),
        LoweredBody::Clauses {
            clauses: body_clauses,
            entries: body_entries,
            ..
        } => (body_clauses, body_entries),
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

    let mut returns: BTreeMap<ControlEntryId, Skeleton> = BTreeMap::new();
    let mut arguments = BTreeMap::new();
    let mut callees = BTreeMap::new();
    for (index, entry) in entries.iter().enumerate() {
        let owner = ControlEntryId::from_u32(index as u32);
        match &entry.tail {
            LoweredTail::Value {
                value,
                dest: ControlDestination::Return,
            } => {
                let contribution = lowering.resolve(*value);
                returns.insert(owner, contribution);
            }
            LoweredTail::DirectCall {
                value,
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
                    returns.insert(
                        owner,
                        Skeleton::Result {
                            callsite: *callsite,
                            value: *value,
                        },
                    );
                }
            }
            LoweredTail::ClosureCall {
                value,
                callsite,
                args,
                dest,
                ..
            } => {
                arguments.insert(
                    *callsite,
                    args.iter().map(|arg| lowering.resolve(arg.value)).collect::<Vec<_>>(),
                );
                if matches!(dest, ControlDestination::Return) {
                    returns.insert(
                        owner,
                        Skeleton::Result {
                            callsite: *callsite,
                            value: *value,
                        },
                    );
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
        returns: Returns::Entries(returns),
        arguments,
        callees,
        input_len: clauses.first().map_or(0, |clause| clause.params.len()),
    }
}

/// An extern body has no steps to walk, so its return is stated outright by
/// the declaration -- but the declaration is not always a leaf: `fz_send`
/// hands its second argument straight back, and its `t` names one and the
/// same type variable in both places. Wherever a parameter's own type is, or
/// contains, a variable the declared return is or contains too, that
/// parameter's value IS the answer, so the skeleton says so with
/// `Skeleton::Input`, which is the only way a caller's own walk can read the
/// relation back out. A return with no such variable stays `Declared`,
/// exactly as before.
///
/// `input_len` travels with the derived arm alone, because it is the length
/// of the answer and not the arity of the function. `returns_input` reads a
/// slot past the end as `true` -- nothing is known about this body, so assume
/// the return can be read back out of every slot -- and that fallback is what
/// keeps a variable-free extern's inputs in its activation key. Sizing the
/// vector here would replace "nothing is known" with "known, and the answer
/// is no slot", erasing those inputs to type variables.
fn extern_skeleton(signature: &LoweredExtern, types: &Types) -> FunctionSkeleton {
    let return_vars = types.free_var_ids(&signature.return_ty);
    let mut returned_params = Skeleton::Bottom;
    if !return_vars.is_empty() {
        for (slot, param_ty) in signature.semantic_contract.params.iter().enumerate() {
            if !types.free_var_ids(param_ty).is_disjoint(&return_vars) {
                returned_params = Skeleton::union(returned_params, Skeleton::Input(slot));
            }
        }
    }
    match returned_params {
        Skeleton::Bottom => FunctionSkeleton {
            returns: Returns::Declared(signature.return_ty),
            ..FunctionSkeleton::default()
        },
        skeleton => FunctionSkeleton {
            returns: Returns::Entries(BTreeMap::from([(ControlEntryId::from_u32(0), skeleton)])),
            input_len: signature.semantic_contract.params.len(),
            ..FunctionSkeleton::default()
        },
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
    Struct(ModuleId, Vec<(MapKey, ValueId)>),
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
            LoweredStep::Struct { value, module, fields } => (
                *value,
                Definition::Struct(
                    *module,
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
            // whatever its operands are still climbing towards, and the
            // walk that reaches it is what says what that is.
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
            // later entry feeds; the turn itself reaches no value.
            return Skeleton::Bottom;
        }
        let definition = self.definitions.get(&value).cloned();
        let skeleton = match definition {
            None => Skeleton::Ground(value),
            Some(definition) => self.resolve_definition(value, &definition),
        };
        self.visiting.remove(&value);
        self.memo.insert(value, skeleton.clone());
        skeleton
    }

    fn resolve_definition(&mut self, value: ValueId, definition: &Definition) -> Skeleton {
        match definition {
            Definition::Input(slot) => Skeleton::Input(*slot),
            Definition::Result(callsite) => Skeleton::Result {
                callsite: *callsite,
                value,
            },
            Definition::Alias(source) => self.resolve(*source),
            Definition::Subject(owner, subject) => self.resolve_subject(*owner, *subject),
            Definition::Delivered(sources) => sources
                .iter()
                .map(|source| self.resolve_definition(value, &source.clone()))
                .fold(Skeleton::Bottom, Skeleton::union),
            Definition::Tuple(items) => Skeleton::Tuple(items.iter().copied().map(|item| self.resolve(item)).collect()),
            // `[]` describes no element at all, so there is nothing here to
            // name: what it denotes is exactly what the walk observed
            // standing at this value.
            Definition::List { items, tail: None } if items.is_empty() => Skeleton::Ground(value),
            Definition::List { items, tail } => {
                let mut element = items
                    .iter()
                    .copied()
                    .map(|item| self.resolve(item))
                    .fold(Skeleton::Bottom, Skeleton::union);
                if let Some(tail) = tail {
                    let tail_element = Skeleton::project(self.resolve(*tail), ProjectStep::ListElement);
                    element = Skeleton::union(element, tail_element);
                }
                Skeleton::List {
                    element: Box::new(element),
                    non_empty: tail.is_none(),
                }
            }
            Definition::Map(fields) => Skeleton::Map(
                fields
                    .iter()
                    .map(|(key, value)| (key.clone(), self.resolve(*value)))
                    .collect(),
            ),
            Definition::Struct(module, fields) => Skeleton::Struct(
                *module,
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
    /// walk reads, so the skeleton reads it with the same steps. A path the
    /// skeleton cannot follow reaches no value here, and the walk's own
    /// observation is what answers instead.
    fn resolve_subject(&mut self, owner: ControlEntryId, subject: crate::dispatch_matrix::SubjectId) -> Skeleton {
        let (root, path) = self.body.dispatch_subject_origin(owner, subject);
        let SubjectOriginRoot::Value(value) = root else {
            return Skeleton::Bottom;
        };
        let mut skeleton = self.resolve(value);
        for kind in path {
            let Some(step) = projection_step(kind) else {
                return Skeleton::Bottom;
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
