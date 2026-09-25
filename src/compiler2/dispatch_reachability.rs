use std::collections::{BTreeSet, HashMap, HashSet};
use std::hash::Hash;

use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::dispatch_matrix::{
    BitstringFieldKind, ComparisonValue, DispatchNode, GraphNodeId, ListRegion, OutcomeId, ProjectionKind, Proof,
    ProofSense, Region, RegionPredicate, SubjectId, SubjectSource,
};
use crate::ground_value::{DispatchShape, GroundValue};

use super::identity::ModuleId;
use crate::modules::identity::ModuleName;

use super::return_skeleton::{BoundSkeleton, Skeleton, Substitution};
use super::semantic::ProjectStep;
use super::types::{Ty, Types};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchReachability {
    pub(crate) outcomes: Vec<OutcomeId>,
    pub(crate) outcome_inputs: Vec<(OutcomeId, Vec<Ty>)>,
    pub(crate) fail_reachable: bool,
    #[cfg(test)]
    pub(crate) visited_states: usize,
    #[cfg(test)]
    pub(crate) max_root_slots: usize,
}

/// The result of restricting one whole row by one existing dispatch proof.
/// An unresolved alternative is recorded separately from an impossible one.
#[derive(Debug)]
pub(crate) struct RefinedRows<R> {
    pub(crate) rows: Vec<R>,
    pub(crate) pending: bool,
}

/// Supplies the meaning of a proof over a complete row. The graph walker is
/// shared; concrete types and source-equation bindings differ only in how a
/// proof restricts their state. Equal rows must denote equal restrictions.
pub(crate) trait DispatchRowDomain {
    type Row: Clone + Eq + Hash;

    fn refine(&mut self, plan: &PatternDispatchPlan<Ty>, row: &Self::Row, proof: &Proof<Ty>) -> RefinedRows<Self::Row>;
}

#[derive(Debug)]
pub(crate) struct DispatchRows<R> {
    pub(crate) outcomes: Vec<(OutcomeId, R)>,
    pub(crate) fail_reachable: bool,
    pub(crate) pending: bool,
    #[cfg(test)]
    pub(crate) visited_states: usize,
}

pub(crate) fn dispatch_rows<D: DispatchRowDomain>(
    domain: &mut D,
    plan: &PatternDispatchPlan<Ty>,
    rows: impl IntoIterator<Item = D::Row>,
) -> DispatchRows<D::Row> {
    let mut walker = DispatchWalker {
        domain,
        plan,
        visited: HashSet::new(),
        seen_outcomes: HashSet::new(),
        outcomes: Vec::new(),
        fail_reachable: false,
        pending: false,
    };
    for row in rows {
        walker.visit(plan.graph.root, row);
    }
    DispatchRows {
        outcomes: walker.outcomes,
        fail_reachable: walker.fail_reachable,
        pending: walker.pending,
        #[cfg(test)]
        visited_states: walker.visited.len(),
    }
}

struct DispatchWalker<'a, D: DispatchRowDomain> {
    domain: &'a mut D,
    plan: &'a PatternDispatchPlan<Ty>,
    visited: HashSet<(GraphNodeId, D::Row)>,
    seen_outcomes: HashSet<(OutcomeId, D::Row)>,
    outcomes: Vec<(OutcomeId, D::Row)>,
    fail_reachable: bool,
    pending: bool,
}

impl<D: DispatchRowDomain> DispatchWalker<'_, D> {
    fn visit(&mut self, node_id: GraphNodeId, row: D::Row) {
        if !self.visited.insert((node_id, row.clone())) {
            return;
        }
        let Some(node) = self.plan.graph.node(node_id) else {
            return;
        };
        match node {
            DispatchNode::Fail => self.fail_reachable = true,
            DispatchNode::Outcome { outcome, .. } => {
                if self.seen_outcomes.insert((*outcome, row.clone())) {
                    self.outcomes.push((*outcome, row));
                }
            }
            DispatchNode::Test { on_match, on_miss, .. } => {
                for next in self.apply_proofs(&row, &on_match.evidence.proofs) {
                    self.visit(on_match.target, next);
                }
                for next in self.apply_proofs(&row, &on_miss.evidence.proofs) {
                    self.visit(on_miss.target, next);
                }
            }
        }
    }

    fn apply_proofs(&mut self, row: &D::Row, proofs: &[Proof<Ty>]) -> Vec<D::Row> {
        let mut rows = vec![row.clone()];
        for proof in proofs {
            let mut next = Vec::new();
            let mut seen = HashSet::new();
            for row in rows {
                let refined = self.domain.refine(self.plan, &row, proof);
                self.pending |= refined.pending;
                for row in refined.rows {
                    if seen.insert(row.clone()) {
                        next.push(row);
                    }
                }
            }
            rows = next;
        }
        rows
    }
}

/// Access to the caller-owned binding arena. A family alternative is a whole
/// substitution; a missing alternative is not an independently unknown column.
pub(crate) trait BoundDispatchSource {
    type Frame: Clone + Eq + Hash;

    fn input_rows(&mut self, frame: &Self::Frame) -> RefinedRows<Substitution<Self::Frame>>;
    fn observed(&mut self, value: &BoundSkeleton<Self::Frame>, types: &mut Types) -> Option<Ty>;
    fn struct_name(&self, module: ModuleId) -> Option<ModuleName>;
    fn rebind(&mut self, frame: &Self::Frame, inputs: &Substitution<Self::Frame>) -> Self::Frame;
}

/// Source producers and restrictions for one dispatch proof. Undemanded
/// roots may remain unexpanded; this is not a semantic application input row.
/// Concrete constraints are proof restrictions, never replacement values.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct BoundDispatchRow<F> {
    pub(crate) substitution: Substitution<F>,
    pub(crate) constraints: Vec<Option<Ty>>,
    list_shapes: Vec<Option<ListRegion>>,
}

impl<F: Clone + Eq + Hash> BoundDispatchRow<F> {
    pub(crate) fn new(plan: &PatternDispatchPlan<Ty>, substitution: Substitution<F>) -> Self {
        assert_eq!(plan.input_count, substitution.arguments.len());
        Self {
            constraints: vec![None; substitution.arguments.len()],
            substitution,
            list_shapes: vec![None; plan.graph.subjects.len()],
        }
    }
}

pub(crate) struct BoundDispatchDomain<'a, S: BoundDispatchSource> {
    pub(crate) types: &'a mut Types,
    pub(crate) source: &'a mut S,
}

enum BoundNeed<F> {
    Family(F),
    Pending,
}

impl<S: BoundDispatchSource> BoundDispatchDomain<'_, S> {
    /// Constructor/projection cancellation retains the producer's frame.
    /// A projected proof constraint travels beside that symbolic value.
    #[cfg(test)]
    fn project(
        &mut self,
        row: &BoundDispatchRow<S::Frame>,
        input: usize,
        step: ProjectStep,
    ) -> (BoundSkeleton<S::Frame>, Option<Ty>) {
        let value = self.resolve(&row.substitution.arguments[input]);
        let value = value.project(step.clone(), &mut |_, _| None);
        let constraint = row.constraints[input].map(|ty| step.apply(self.types, ty));
        (value, constraint)
    }

    #[cfg(test)]
    fn resolve(&mut self, value: &BoundSkeleton<S::Frame>) -> BoundSkeleton<S::Frame> {
        value.resolve(&mut |frame, slot| {
            let mut family = self.source.input_rows(frame);
            if !family.pending && family.rows.len() == 1 {
                family.rows.pop().and_then(|row| row.arguments.get(slot).cloned())
            } else {
                None
            }
        })
    }

    fn subject(
        &mut self,
        plan: &PatternDispatchPlan<Ty>,
        row: &BoundDispatchRow<S::Frame>,
        subject: SubjectId,
    ) -> Option<BoundSkeleton<S::Frame>> {
        match plan.subject(subject) {
            SubjectSource::Input { ordinal } => row.substitution.arguments.get(*ordinal as usize).cloned(),
            SubjectSource::Projection(projection) => {
                let source = self.subject(plan, row, projection.source)?;
                let step = match &projection.kind {
                    ProjectionKind::TupleField(index) => ProjectStep::TupleField(*index as usize),
                    ProjectionKind::StructField(name) => {
                        ProjectStep::MapField(super::types::MapKey::Atom(name.clone()))
                    }
                    ProjectionKind::MapValue { key } => ProjectStep::MapField(key.as_map_key()?),
                    ProjectionKind::ListHead => ProjectStep::ListElement,
                    ProjectionKind::ListTail => ProjectStep::ListTail,
                    ProjectionKind::BitstringField(_) => return None,
                };
                Some(source.project(step, &mut |_, _| None))
            }
        }
    }

    /// These envelopes answer universal dispatch questions only. Family
    /// choices remain inexact: an ambiguous proof must select a whole row.
    fn view(
        &mut self,
        bound: &BoundSkeleton<S::Frame>,
        active: &mut HashMap<BoundSkeleton<S::Frame>, usize>,
    ) -> (Ty, bool) {
        self.view_at_depth(bound, active, 0)
    }

    fn view_at_depth(
        &mut self,
        bound: &BoundSkeleton<S::Frame>,
        active: &mut HashMap<BoundSkeleton<S::Frame>, usize>,
        depth: usize,
    ) -> (Ty, bool) {
        if let Some(previous_depth) = active.get(bound) {
            // An unguarded alias adds no branch. Recurrence beneath a
            // constructor may add arbitrarily deep values, all covered by
            // this temporary top envelope; it is never settled evidence.
            return (
                if *previous_depth == depth {
                    self.types.none()
                } else {
                    self.types.any()
                },
                false,
            );
        }
        active.insert(bound.clone(), depth);
        let value = bound.resolve(&mut |_, _| None);
        if let Some(observed) = self.source.observed(&value, self.types) {
            active.remove(bound);
            return (observed, true);
        }
        let child = |shape: &Skeleton| BoundSkeleton::new(value.frame.clone(), shape.clone());
        let answer = match &value.shape {
            Skeleton::Bottom => (self.types.none(), true),
            Skeleton::Input(slot) => {
                let family = self.source.input_rows(&value.frame);
                let mut joined = if family.pending {
                    self.types.any()
                } else {
                    self.types.none()
                };
                for row in family.rows {
                    let Some(input) = row.arguments.get(*slot) else {
                        joined = self.types.any();
                        continue;
                    };
                    let (ty, _) = self.view_at_depth(input, active, depth);
                    joined = self.types.union(joined, ty);
                }
                (joined, false)
            }
            Skeleton::Ground(_) | Skeleton::Result { .. } => self
                .source
                .observed(&value, self.types)
                .map(|ty| (ty, true))
                .unwrap_or_else(|| (self.types.any(), false)),
            Skeleton::Tuple(fields) => {
                let views = fields
                    .iter()
                    .map(|shape| self.view_at_depth(&child(shape), active, depth + 1))
                    .collect::<Vec<_>>();
                let tys = views.iter().map(|(ty, _)| *ty).collect::<Vec<_>>();
                (self.types.tuple(&tys), views.iter().all(|(_, exact)| *exact))
            }
            Skeleton::List { element, non_empty } => {
                let (element, exact) = self.view_at_depth(&child(element), active, depth + 1);
                let ty = if *non_empty {
                    self.types.non_empty_list(element)
                } else {
                    self.types.list(element)
                };
                (ty, exact)
            }
            Skeleton::Map(fields) => {
                let views = fields
                    .iter()
                    .map(|(key, shape)| (key.clone(), self.view_at_depth(&child(shape), active, depth + 1)))
                    .collect::<Vec<_>>();
                let fields = views
                    .iter()
                    .map(|(key, (ty, _))| (key.clone(), *ty))
                    .collect::<Vec<_>>();
                (self.types.map(&fields), views.iter().all(|(_, (_, exact))| *exact))
            }
            Skeleton::Struct(module, fields) => {
                if let Some(name) = self.source.struct_name(*module) {
                    let views = fields
                        .iter()
                        .map(|(key, shape)| (key.clone(), self.view_at_depth(&child(shape), active, depth + 1)))
                        .collect::<Vec<_>>();
                    let fields = views
                        .iter()
                        .map(|(key, (ty, _))| (key.clone(), *ty))
                        .collect::<Vec<_>>();
                    (
                        self.types.struct_map(*module, name, &fields),
                        views.iter().all(|(_, (_, exact))| *exact),
                    )
                } else {
                    (self.types.any(), false)
                }
            }
            Skeleton::Union(branches) => {
                let mut joined = self.types.none();
                let mut exact = true;
                for shape in branches {
                    let (ty, known) = self.view_at_depth(&child(shape), active, depth);
                    joined = self.types.union(joined, ty);
                    exact &= known;
                }
                (joined, exact)
            }
            Skeleton::Project { of, step } => {
                let (ty, exact) = self.view_at_depth(&child(of), active, depth);
                (step.apply(self.types, ty), exact)
            }
        };
        active.remove(bound);
        answer
    }

    fn need(&mut self, bound: &BoundSkeleton<S::Frame>) -> BoundNeed<S::Frame> {
        // Choosing an input family is the joint operation performed by the
        // caller. Do not walk its single recursive alternative separately in
        // each column while looking for the next unresolved observation.
        let value = bound.resolve(&mut |_, _| None);
        match &value.shape {
            Skeleton::Input(_) => BoundNeed::Family(value.frame),
            Skeleton::Project { of, .. } => self.need(&BoundSkeleton::new(value.frame.clone(), (**of).clone())),
            Skeleton::Tuple(fields) | Skeleton::Union(fields) => {
                for shape in fields {
                    let child = BoundSkeleton::new(value.frame.clone(), shape.clone());
                    if !self.view(&child, &mut HashMap::new()).1 {
                        return self.need(&child);
                    }
                }
                BoundNeed::Pending
            }
            Skeleton::List { element, .. } => self.need(&BoundSkeleton::new(value.frame.clone(), (**element).clone())),
            Skeleton::Map(fields) | Skeleton::Struct(_, fields) => {
                for (_, shape) in fields {
                    let child = BoundSkeleton::new(value.frame.clone(), shape.clone());
                    if !self.view(&child, &mut HashMap::new()).1 {
                        return self.need(&child);
                    }
                }
                BoundNeed::Pending
            }
            Skeleton::Ground(_) | Skeleton::Result { .. } | Skeleton::Bottom => BoundNeed::Pending,
        }
    }
}

impl<S: BoundDispatchSource> DispatchRowDomain for BoundDispatchDomain<'_, S> {
    type Row = BoundDispatchRow<S::Frame>;

    fn refine(&mut self, plan: &PatternDispatchPlan<Ty>, row: &Self::Row, proof: &Proof<Ty>) -> RefinedRows<Self::Row> {
        let mut work = vec![row.clone()];
        let mut seen = HashSet::new();
        let mut answer = RefinedRows {
            rows: Vec::new(),
            pending: false,
        };
        while let Some(row) = work.pop() {
            if !seen.insert(row.clone()) {
                continue;
            }
            let roots = row
                .substitution
                .arguments
                .iter()
                .enumerate()
                .map(|(slot, bound)| {
                    let (view, _) = self.view(bound, &mut HashMap::new());
                    row.constraints[slot]
                        .map(|constraint| self.types.intersect(view, constraint))
                        .unwrap_or(view)
                })
                .collect::<Vec<_>>();
            if roots.iter().any(|root| self.types.is_empty(root)) {
                continue;
            }
            let subject = self.subject(plan, &row, proof.predicate.subject);
            let target = predicate_target(self.types, &proof.predicate.region);
            let mut universal = None;
            let needed = match (subject.as_ref(), target) {
                (Some(subject), Some(target)) => {
                    let (view, exact) = self.view(subject, &mut HashMap::new());
                    let overlap = self.types.intersect(view, target.ty);
                    if exact {
                        false
                    } else if self.types.is_empty(&overlap) {
                        universal = Some(false);
                        false
                    } else if self.types.is_subtype(&view, &target.ty) {
                        universal = Some(true);
                        false
                    } else {
                        true
                    }
                }
                _ => false,
            };
            if let Some(holds) = universal {
                if holds == matches!(proof.sense, ProofSense::Holds) {
                    let mut next = row;
                    let mut concrete = ConcreteDispatchRows { types: self.types };
                    if concrete
                        .record_list_shape(
                            plan,
                            &roots,
                            &mut next.list_shapes,
                            &proof.predicate,
                            proof.predicate.subject,
                            proof.sense,
                        )
                        .is_some()
                    {
                        answer.rows.push(next);
                    }
                }
                continue;
            }
            if needed {
                match self.need(subject.as_ref().expect("only symbolic subjects need expansion")) {
                    BoundNeed::Pending => answer.pending = true,
                    BoundNeed::Family(frame) => {
                        let family = self.source.input_rows(&frame);
                        answer.pending |= family.pending;
                        for replacement in family.rows {
                            let mut next = row.clone();
                            next.substitution =
                                row.substitution
                                    .apply_once(&frame, &replacement, &mut |frame, replacement| {
                                        self.source.rebind(frame, replacement)
                                    });
                            // This domain proves clause reachability only. A
                            // root no test reads cannot distinguish outcomes;
                            // retain its source reference rather than unfold
                            // an irrelevant recursive constructor history.
                            for (slot, argument) in next.substitution.arguments.iter_mut().enumerate() {
                                if !plan.required_input(slot) {
                                    *argument = row.substitution.arguments[slot].clone();
                                }
                            }
                            work.push(next);
                        }
                    }
                }
                continue;
            }
            let mut concrete = ConcreteDispatchRows { types: self.types };
            let refined = concrete.refine(
                plan,
                &ReachabilityState {
                    roots: roots.clone(),
                    list_shapes: row.list_shapes.clone(),
                },
                proof,
            );
            for state in refined.rows {
                let mut next = row.clone();
                for (slot, constrained) in state.roots.into_iter().enumerate() {
                    if constrained != roots[slot] {
                        next.constraints[slot] = Some(constrained);
                    }
                }
                next.list_shapes = state.list_shapes;
                answer.rows.push(next);
            }
        }
        answer
    }
}

pub(crate) fn calculate_dispatch_reachability(
    types: &mut Types,
    plan: &PatternDispatchPlan<Ty>,
    inputs: &[Ty],
) -> DispatchReachability {
    let any = types.any();
    // The runtime envelope answers "what could this be at runtime", which is
    // `any` for a type variable -- right for deciding reachability, since no
    // runtime test can test a variable. But these same roots are refined into
    // `outcome_inputs`, which TYPES each clause's parameters, and there a
    // variable means not-yet-known rather than "anything". Envelope only the
    // slots some test actually looks at: a slot no test names cannot change
    // any outcome, so passing it through unchanged keeps the fixpoint's
    // pending bindings intact (fz-f98.14.11).
    let roots = (0..plan.input_count)
        .map(|ordinal| {
            let input = inputs.get(ordinal).copied().unwrap_or(any);
            if plan.required_input(ordinal) {
                types.runtime_envelope(input)
            } else {
                input
            }
        })
        .collect::<Vec<_>>();
    let list_shapes = vec![None; plan.graph.subjects.len()];
    let mut domain = ConcreteDispatchRows { types };
    let reached = dispatch_rows(&mut domain, plan, [ReachabilityState { roots, list_shapes }]);
    debug_assert!(!reached.pending, "concrete type restrictions are always answerable");
    let outcomes = reached
        .outcomes
        .iter()
        .map(|(outcome, _)| *outcome)
        .collect::<BTreeSet<_>>();
    let outcome_inputs = reached
        .outcomes
        .into_iter()
        .map(|(outcome, row)| (outcome, row.roots))
        .collect::<BTreeSet<_>>();
    DispatchReachability {
        outcomes: outcomes.into_iter().collect(),
        outcome_inputs: outcome_inputs.into_iter().collect(),
        fail_reachable: reached.fail_reachable,
        #[cfg(test)]
        visited_states: reached.visited_states,
        #[cfg(test)]
        max_root_slots: plan.input_count,
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ReachabilityState {
    roots: Vec<Ty>,
    list_shapes: Vec<Option<ListRegion>>,
}

struct ConcreteDispatchRows<'a> {
    types: &'a mut Types,
}

impl DispatchRowDomain for ConcreteDispatchRows<'_> {
    type Row = ReachabilityState;

    fn refine(&mut self, plan: &PatternDispatchPlan<Ty>, row: &Self::Row, proof: &Proof<Ty>) -> RefinedRows<Self::Row> {
        RefinedRows {
            rows: self
                .apply_proof(plan, row.clone(), &proof.predicate, proof.sense)
                .into_iter()
                .collect(),
            pending: false,
        }
    }
}

impl ConcreteDispatchRows<'_> {
    fn apply_proof(
        &mut self,
        plan: &PatternDispatchPlan<Ty>,
        mut state: ReachabilityState,
        predicate: &RegionPredicate<Ty>,
        sense: ProofSense,
    ) -> Option<ReachabilityState> {
        let subject = predicate.subject;
        self.record_list_shape(plan, &state.roots, &mut state.list_shapes, predicate, subject, sense)?;
        let Some(target) = predicate_target(self.types, &predicate.region) else {
            return Some(state);
        };
        let ordinal = subject_input(plan, subject)?;
        let root = *state.roots.get(ordinal)?;
        let alternatives = self.types.projection_alternatives(root);
        let mut matched = None;
        let mut missed = None;
        for alternative in alternatives {
            let mut row = state.roots.clone();
            row[ordinal] = alternative;
            let projected = project_subject(self.types, plan, &row, subject);
            let overlap = self.types.intersect(projected, target.ty);
            if self.types.is_empty(&overlap) {
                missed = join_optional(self.types, missed, alternative);
                continue;
            }
            if self.types.is_subtype(&projected, &target.ty) {
                matched = join_optional(self.types, matched, alternative);
                continue;
            }
            if target.exact
                && exact_projection_path(plan, subject)
                && let Some((lifted_ordinal, lifted)) =
                    lift_projection_constraint(self.types, plan, &row, subject, target.ty)
            {
                debug_assert_eq!(lifted_ordinal, ordinal);
                let match_alternative = self.types.intersect(alternative, lifted);
                if !self.types.is_empty(&match_alternative) {
                    matched = join_optional(self.types, matched, match_alternative);
                }
                let miss_alternative = self.types.difference(alternative, lifted);
                if !self.types.is_empty(&miss_alternative) {
                    missed = join_optional(self.types, missed, miss_alternative);
                }
                continue;
            }
            // A positional or value-only projection is not representable in
            // the root type. Retain the original alternative on both edges.
            matched = join_optional(self.types, matched, alternative);
            missed = join_optional(self.types, missed, alternative);
        }
        let selected = match sense {
            ProofSense::Holds => matched,
            ProofSense::DoesNotHold => missed,
        }?;
        state.roots[ordinal] = selected;
        Some(state)
    }

    fn record_list_shape(
        &mut self,
        plan: &PatternDispatchPlan<Ty>,
        roots: &[Ty],
        list_shapes: &mut [Option<ListRegion>],
        predicate: &RegionPredicate<Ty>,
        subject: SubjectId,
        sense: ProofSense,
    ) -> Option<()> {
        let Region::List(region) = predicate.region else {
            return Some(());
        };
        let known = match sense {
            ProofSense::Holds => region,
            ProofSense::DoesNotHold => {
                let projected = project_subject(self.types, plan, roots, subject);
                let any = self.types.any();
                let proper_list = self.types.list(any);
                if !self.types.is_subtype(&projected, &proper_list) {
                    return Some(());
                }
                match region {
                    ListRegion::Empty => ListRegion::Cons,
                    ListRegion::Cons => ListRegion::Empty,
                }
            }
        };
        let slot = list_shapes.get_mut(predicate.subject.0 as usize)?;
        match slot {
            Some(previous) if *previous != known => None,
            Some(_) => Some(()),
            None => {
                *slot = Some(known);
                Some(())
            }
        }
    }
}

#[derive(Clone, Copy)]
struct PredicateTarget {
    ty: Ty,
    exact: bool,
}

fn predicate_target(types: &mut Types, region: &Region<Ty>) -> Option<PredicateTarget> {
    let exact = true;
    let ty = match region {
        Region::Type(ty) => *ty,
        Region::Equal(ComparisonValue::Const(value)) => match value.as_dispatch_shape()? {
            DispatchShape::Atom(name) => types.atom_lit(name),
            DispatchShape::Bool(value) => types.bool_lit(value),
            DispatchShape::Nil => types.nil(),
            DispatchShape::Int(_) | DispatchShape::Float(_) | DispatchShape::Utf8Binary(_) => return None,
        },
        Region::Equal(ComparisonValue::Pinned(_)) | Region::Guard(_) | Region::Bitstring(_) => return None,
        Region::TupleArity(arity) => {
            let any = types.any();
            let fields = types.repeat(any, *arity as usize);
            types.tuple(&fields)
        }
        Region::List(ListRegion::Empty) => types.empty_list(),
        Region::List(ListRegion::Cons) => {
            let any = types.any();
            types.non_empty_list(any)
        }
        Region::MapKind => types.map_top(),
        Region::MapKeyPresent { key } => {
            let map_key = match key {
                GroundValue::Atom(name) => crate::ground_value::MapKey::Atom(name.clone()),
                GroundValue::Nil => crate::ground_value::MapKey::Atom("nil".to_string()),
                GroundValue::Int(_)
                | GroundValue::Float(_)
                | GroundValue::Bool(_)
                | GroundValue::Binary(_)
                | GroundValue::Utf8Binary(_) => return None,
            };
            let any = types.any();
            return Some(PredicateTarget {
                ty: types.map(&[(map_key, any)]),
                exact: false,
            });
        }
    };
    Some(PredicateTarget { ty, exact })
}

fn subject_input(plan: &PatternDispatchPlan<Ty>, subject: SubjectId) -> Option<usize> {
    match plan.subject(subject) {
        SubjectSource::Input { ordinal } => Some(*ordinal as usize),
        SubjectSource::Projection(projection) => subject_input(plan, projection.source),
    }
}

fn exact_projection_path(plan: &PatternDispatchPlan<Ty>, subject: SubjectId) -> bool {
    match plan.subject(subject) {
        SubjectSource::Input { .. } => true,
        SubjectSource::Projection(projection) => {
            matches!(
                projection.kind,
                ProjectionKind::TupleField(_) | ProjectionKind::StructField(_)
            ) && exact_projection_path(plan, projection.source)
        }
    }
}

pub(crate) fn project_subject(
    types: &mut Types,
    plan: &PatternDispatchPlan<Ty>,
    roots: &[Ty],
    subject: SubjectId,
) -> Ty {
    let SubjectSource::Projection(projection) = plan.subject(subject) else {
        let SubjectSource::Input { ordinal } = plan.subject(subject) else {
            unreachable!()
        };
        return roots.get(*ordinal as usize).copied().unwrap_or_else(|| types.any());
    };
    let source = project_subject(types, plan, roots, projection.source);
    match &projection.kind {
        ProjectionKind::TupleField(index) => types.tuple_field_type(&source, *index as usize),
        ProjectionKind::StructField(field) => types
            .map_field_lookup(&source, &crate::types::MapKey::Atom(field.clone()))
            .unwrap_or_else(|| types.any()),
        ProjectionKind::ListHead => types.list_element_type(&source),
        ProjectionKind::ListTail => {
            let element = types.list_element_type(&source);
            types.list(element)
        }
        ProjectionKind::MapValue { key } => key
            .as_map_key()
            .and_then(|key| types.map_field_lookup(&source, &key))
            .unwrap_or_else(|| types.any()),
        ProjectionKind::BitstringField(extraction) => match extraction.spec.kind {
            BitstringFieldKind::Integer
            | BitstringFieldKind::Utf8
            | BitstringFieldKind::Utf16
            | BitstringFieldKind::Utf32 => types.int(),
            BitstringFieldKind::Float => types.float(),
            BitstringFieldKind::Binary => types.str_t(),
            BitstringFieldKind::Bits => types.str_t(),
        },
    }
}

fn lift_projection_constraint(
    types: &mut Types,
    plan: &PatternDispatchPlan<Ty>,
    roots: &[Ty],
    subject: SubjectId,
    constraint: Ty,
) -> Option<(usize, Ty)> {
    match plan.subject(subject) {
        SubjectSource::Input { ordinal } => Some((*ordinal as usize, constraint)),
        SubjectSource::Projection(projection) => {
            let source = projection.source;
            let source_ty = project_subject(types, plan, roots, source);
            let constrained = match &projection.kind {
                ProjectionKind::StructField(field) => {
                    types.refine_map_field(&source_ty, &crate::types::MapKey::Atom(field.clone()), &constraint)
                }
                ProjectionKind::TupleField(index) => {
                    let arity = types.max_tuple_arity(&source_ty);
                    if *index as usize >= arity {
                        return None;
                    }
                    let any = types.any();
                    let mut fields = types.repeat(any, arity);
                    fields[*index as usize] = constraint;
                    types.tuple(&fields)
                }
                _ => return None,
            };
            lift_projection_constraint(types, plan, roots, source, constrained)
        }
    }
}

fn join_optional(types: &mut Types, current: Option<Ty>, next: Ty) -> Option<Ty> {
    Some(match current {
        Some(current) => types.union(current, next),
        None => next,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Expr, Pattern, Spanned};
    use crate::compiler2::types::{MapKey, Sigma, TypeVarId};
    use crate::dispatch_matrix::demand::DispatchDemand;
    use crate::dispatch_matrix::pattern::{
        PatternRow, PatternSubjectRef, SourcePatternRows, pattern_dispatch_from_source,
    };

    fn row(pattern: Pattern, body_id: u32) -> PatternRow<Ty> {
        PatternRow {
            patterns: vec![Spanned::dummy(pattern)],
            preconditions: Vec::new(),
            guard: None,
            body_id,
        }
    }

    fn row2(first: Pattern, second: Pattern, body_id: u32) -> PatternRow<Ty> {
        PatternRow {
            patterns: vec![Spanned::dummy(first), Spanned::dummy(second)],
            preconditions: Vec::new(),
            guard: None,
            body_id,
        }
    }

    #[derive(Default)]
    struct SymbolicSource {
        families: std::collections::HashMap<usize, (Vec<Substitution<usize>>, bool)>,
        observations: std::collections::HashMap<BoundSkeleton<usize>, Ty>,
        rebound: Vec<(usize, Substitution<usize>)>,
        struct_names: HashMap<ModuleId, ModuleName>,
        lookup_limit: Option<usize>,
        lookups: usize,
    }

    impl BoundDispatchSource for SymbolicSource {
        type Frame = usize;

        fn input_rows(&mut self, frame: &usize) -> RefinedRows<Substitution<usize>> {
            self.lookups += 1;
            if let Some(limit) = self.lookup_limit {
                assert!(
                    self.lookups <= limit,
                    "dispatch proof enumerated a recursive producer history"
                );
            }
            match self.families.get(frame) {
                Some((rows, pending)) => RefinedRows {
                    rows: rows.clone(),
                    pending: *pending,
                },
                None => RefinedRows {
                    rows: Vec::new(),
                    pending: true,
                },
            }
        }

        fn observed(&mut self, value: &BoundSkeleton<usize>, _types: &mut Types) -> Option<Ty> {
            self.observations.get(value).copied()
        }

        fn struct_name(&self, module: ModuleId) -> Option<ModuleName> {
            self.struct_names.get(&module).cloned()
        }

        fn rebind(&mut self, frame: &usize, inputs: &Substitution<usize>) -> usize {
            if let Some(index) = self.rebound.iter().position(|entry| entry == &(*frame, inputs.clone())) {
                return 100 + index;
            }
            let next = 100 + self.rebound.len();
            self.rebound.push((*frame, inputs.clone()));
            self.families.insert(next, (vec![inputs.clone()], false));
            next
        }
    }

    fn aligned_plan() -> PatternDispatchPlan<Ty> {
        pattern_dispatch_from_source(SourcePatternRows::lexical(
            2,
            vec![
                row2(Pattern::Atom("left".into()), Pattern::Atom("right".into()), 0),
                row2(
                    Pattern::Tuple(vec![Spanned::dummy(Pattern::Wildcard)]),
                    Pattern::Tuple(vec![Spanned::dummy(Pattern::Wildcard)]),
                    1,
                ),
                row2(Pattern::Wildcard, Pattern::Wildcard, 2),
            ],
        ))
        .unwrap()
    }

    #[test]
    fn bound_dispatch_selects_one_recursive_producer_row_for_both_columns() {
        let plan = aligned_plan();
        let mut types = Types::new();
        let left = types.atom_lit("left");
        let right = types.atom_lit("right");
        let seed = Substitution::in_frame(1, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let recur = Substitution::in_frame(
            0,
            &[
                Skeleton::Tuple(vec![Skeleton::Input(0)]),
                Skeleton::Tuple(vec![Skeleton::Input(1)]),
            ],
        );
        let inputs = Substitution::in_frame(0, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let mut source = SymbolicSource::default();
        source.families.insert(0, (vec![seed.clone(), recur], false));
        source.families.insert(1, (vec![seed.clone()], false));
        source.observations.insert(seed.arguments[0].clone(), left);
        source.observations.insert(seed.arguments[1].clone(), right);
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let reached = dispatch_rows(&mut domain, &plan, [BoundDispatchRow::new(&plan, inputs.clone())]);
        assert!(!reached.pending);
        assert!(!reached.fail_reachable);
        assert_eq!(reached.outcomes.len(), 2);
        for (outcome, row) in reached.outcomes {
            match plan.outcome(outcome).unwrap().body_id {
                0 => assert_eq!(row.substitution, seed),
                1 => {
                    for slot in 0..2 {
                        let (projected, constraint) = domain.project(&row, slot, ProjectStep::TupleField(0));
                        assert_eq!(projected, inputs.arguments[slot]);
                        assert_eq!(
                            constraint, None,
                            "known constructors require no invented marginal restriction"
                        );
                    }
                }
                _ => panic!("equal-depth alternatives cannot reach the crossed fallback"),
            }
        }
        let mismatched = Substitution {
            arguments: vec![
                seed.arguments[0].clone(),
                BoundSkeleton::new(0, Skeleton::Tuple(vec![Skeleton::Input(1)])),
            ],
        };
        let reached = dispatch_rows(&mut domain, &plan, [BoundDispatchRow::new(&plan, mismatched)]);
        assert!(!reached.pending);
        assert_eq!(reached.outcomes.len(), 1);
        assert_eq!(plan.outcome(reached.outcomes[0].0).unwrap().body_id, 2);
    }

    #[test]
    fn bound_dispatch_proves_unchanged_column_without_unfolding_growing_sibling() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            2,
            vec![
                row2(Pattern::Wildcard, Pattern::Atom("right".into()), 0),
                row2(Pattern::Wildcard, Pattern::Wildcard, 1),
            ],
        ))
        .unwrap();
        let mut types = Types::new();
        let left = types.atom_lit("left");
        let right = types.atom_lit("right");
        let seed = Substitution::in_frame(1, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let recur = Substitution::in_frame(0, &[Skeleton::Tuple(vec![Skeleton::Input(0)]), Skeleton::Input(1)]);
        let inputs = Substitution::in_frame(0, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let mut source = SymbolicSource::default();
        source.families.insert(0, (vec![seed.clone(), recur], false));
        source.observations.insert(seed.arguments[0].clone(), left);
        source.observations.insert(seed.arguments[1].clone(), right);
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let (envelope, exact) = domain.view(&inputs.arguments[1], &mut HashMap::new());
        assert_eq!(envelope, right, "an unguarded self alias adds no new branch");
        assert!(!exact, "a family envelope never becomes settled input evidence");
        let reached = dispatch_rows(&mut domain, &plan, [BoundDispatchRow::new(&plan, inputs.clone())]);
        assert!(!reached.pending);
        assert_eq!(reached.outcomes.len(), 1);
        assert_eq!(plan.outcome(reached.outcomes[0].0).unwrap().body_id, 0);
        assert_eq!(reached.outcomes[0].1.substitution, inputs);
        assert_eq!(reached.outcomes[0].1.constraints, vec![None, None]);
        assert!(reached.visited_states <= plan.graph.nodes.len());
    }

    #[test]
    fn bound_dispatch_ambiguous_column_envelopes_still_choose_one_opposite_seed_row() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            2,
            vec![
                row2(Pattern::Atom("left".into()), Pattern::Atom("left".into()), 0),
                row2(Pattern::Wildcard, Pattern::Wildcard, 1),
            ],
        ))
        .unwrap();
        let mut types = Types::new();
        let left = types.atom_lit("left");
        let right = types.atom_lit("right");
        let first = Substitution::in_frame(1, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let second = Substitution::in_frame(2, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let mut source = SymbolicSource::default();
        source.families.insert(0, (vec![first.clone(), second.clone()], false));
        for (row, values) in [(&first, [left, right]), (&second, [right, left])] {
            for (bound, ty) in row.arguments.iter().zip(values) {
                source.observations.insert(bound.clone(), ty);
            }
        }
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let input = BoundDispatchRow::new(
            &plan,
            Substitution::in_frame(0, &[Skeleton::Input(0), Skeleton::Input(1)]),
        );
        let reached = dispatch_rows(&mut domain, &plan, [input]);
        assert!(!reached.pending);
        assert_eq!(reached.outcomes.len(), 2);
        for (outcome, row) in reached.outcomes {
            assert_eq!(plan.outcome(outcome).unwrap().body_id, 1);
            assert!(row.substitution == first || row.substitution == second);
            assert_eq!(row.constraints, vec![None, None]);
        }
    }

    #[test]
    fn bound_dispatch_ambiguous_unchanged_column_does_not_expand_unread_growing_root() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            2,
            vec![
                row2(Pattern::Wildcard, Pattern::Atom("left".into()), 0),
                row2(Pattern::Wildcard, Pattern::Wildcard, 1),
            ],
        ))
        .unwrap();
        assert!(!plan.required_input(0));
        let mut types = Types::new();
        let left = types.atom_lit("left");
        let right = types.atom_lit("right");
        let first = Substitution::in_frame(1, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let second = Substitution::in_frame(2, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let recur = Substitution::in_frame(0, &[Skeleton::Tuple(vec![Skeleton::Input(0)]), Skeleton::Input(1)]);
        let mut source = SymbolicSource {
            lookup_limit: Some(256),
            ..SymbolicSource::default()
        };
        source
            .families
            .insert(0, (vec![first.clone(), second.clone(), recur], false));
        for (row, values) in [(&first, [left, right]), (&second, [right, left])] {
            for (bound, ty) in row.arguments.iter().zip(values) {
                source.observations.insert(bound.clone(), ty);
            }
        }
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let inputs = Substitution::in_frame(0, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let reached = dispatch_rows(&mut domain, &plan, [BoundDispatchRow::new(&plan, inputs.clone())]);
        assert!(!reached.pending);
        assert_eq!(reached.outcomes.len(), 2);
        let mut clauses = Vec::new();
        for (outcome, row) in reached.outcomes {
            clauses.push(plan.outcome(outcome).unwrap().body_id);
            assert_eq!(row.substitution.arguments[0], inputs.arguments[0]);
            assert_eq!(row.constraints, vec![None, None]);
        }
        clauses.sort_unstable();
        assert_eq!(clauses, vec![0, 1]);
    }

    #[test]
    fn bound_dispatch_recursive_list_tail_reuses_the_same_demanded_proof() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            2,
            vec![
                row2(list_pattern(0, false), Pattern::Wildcard, 0),
                row2(list_pattern(1, true), Pattern::Wildcard, 1),
            ],
        ))
        .unwrap();
        assert!(!plan.required_input(1));
        let mut types = Types::new();
        let integer = types.int();
        let list = types.list(integer);
        let empty = types.empty_list();
        let seed = Substitution::in_frame(1, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let recur = Substitution::in_frame(
            0,
            &[
                Skeleton::project(Skeleton::Input(0), ProjectStep::ListTail),
                Skeleton::List {
                    element: Box::new(Skeleton::Union(vec![
                        Skeleton::project(Skeleton::Input(0), ProjectStep::ListElement),
                        Skeleton::project(Skeleton::Input(1), ProjectStep::ListElement),
                    ])),
                    non_empty: false,
                },
            ],
        );
        let mut source = SymbolicSource {
            lookup_limit: Some(256),
            ..SymbolicSource::default()
        };
        source.families.insert(0, (vec![recur.clone(), seed.clone()], false));
        source.observations.insert(seed.arguments[0].clone(), list);
        source.observations.insert(seed.arguments[1].clone(), empty);
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let rows = [recur, seed].into_iter().map(|row| BoundDispatchRow::new(&plan, row));
        let reached = dispatch_rows(&mut domain, &plan, rows);
        assert!(!reached.pending);
        let mut clauses = reached
            .outcomes
            .iter()
            .map(|(outcome, _)| plan.outcome(*outcome).unwrap().body_id)
            .collect::<Vec<_>>();
        clauses.sort_unstable();
        clauses.dedup();
        assert_eq!(clauses, vec![0, 1]);
    }

    #[test]
    fn bound_dispatch_struct_envelope_uses_the_source_module_identity() {
        let mut types = Types::new();
        let name = ModuleName::parse_dotted("Box").unwrap();
        let module = ModuleId::GLOBAL;
        let expected = types.struct_map(module, name.clone(), &[]);
        let mut source = SymbolicSource::default();
        source.struct_names.insert(module, name);
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let bound = BoundSkeleton::new(0, Skeleton::Struct(module, Vec::new()));
        let (envelope, exact) = domain.view(&bound, &mut HashMap::new());
        assert_eq!(envelope, expected);
        assert!(exact);
    }

    #[test]
    fn bound_dispatch_distinguishes_pending_family_from_closed_empty_family() {
        let plan = aligned_plan();
        let mut types = Types::new();
        let mut source = SymbolicSource::default();
        let input = BoundDispatchRow::new(
            &plan,
            Substitution::in_frame(0, &[Skeleton::Input(0), Skeleton::Input(1)]),
        );
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let pending = dispatch_rows(&mut domain, &plan, [input.clone()]);
        assert!(pending.pending);
        assert!(pending.outcomes.is_empty());
        assert!(!pending.fail_reachable);
        domain.source.families.insert(0, (Vec::new(), false));
        let empty = dispatch_rows(&mut domain, &plan, [input]);
        assert!(!empty.pending);
        assert!(empty.outcomes.is_empty());
        assert!(!empty.fail_reachable);
    }

    #[test]
    fn bound_dispatch_preserves_known_rows_beside_pending_alternatives() {
        let plan = aligned_plan();
        let mut types = Types::new();
        let seed = Substitution::in_frame(1, &[Skeleton::Input(0), Skeleton::Input(1)]);
        let mut source = SymbolicSource::default();
        source.families.insert(0, (vec![seed.clone()], true));
        source
            .observations
            .insert(seed.arguments[0].clone(), types.atom_lit("left"));
        source
            .observations
            .insert(seed.arguments[1].clone(), types.atom_lit("right"));
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let row = BoundDispatchRow::new(
            &plan,
            Substitution::in_frame(0, &[Skeleton::Input(0), Skeleton::Input(1)]),
        );
        let reached = dispatch_rows(&mut domain, &plan, [row]);
        assert!(reached.pending);
        assert!(!reached.fail_reachable);
        assert_eq!(reached.outcomes.len(), 1);
        assert_eq!(plan.outcome(reached.outcomes[0].0).unwrap().body_id, 0);
        assert_eq!(reached.outcomes[0].1.substitution, seed);
    }

    #[test]
    fn bound_dispatch_does_not_observe_an_unresolved_struct_as_a_plain_map() {
        let mut types = Types::new();
        let mut source = SymbolicSource::default();
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let bound = BoundSkeleton::new(0, Skeleton::Struct(super::super::ModuleId::GLOBAL, Vec::new()));
        let (envelope, exact) = domain.view(&bound, &mut HashMap::new());
        assert!(!exact);
        assert_eq!(envelope, domain.types.any());
    }

    #[test]
    fn bound_dispatch_keeps_type_restrictions_beside_the_original_producer() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![row(Pattern::Atom("left".into()), 0), row(Pattern::Wildcard, 1)],
        ))
        .unwrap();
        let mut types = Types::new();
        let left = types.atom_lit("left");
        let right = types.atom_lit("right");
        let either = types.union(left, right);
        let value = BoundSkeleton::new(1, Skeleton::Input(0));
        let mut source = SymbolicSource::default();
        source.observations.insert(value.clone(), either);
        let mut domain = BoundDispatchDomain {
            types: &mut types,
            source: &mut source,
        };
        let row = BoundDispatchRow::new(
            &plan,
            Substitution {
                arguments: vec![value.clone()],
            },
        );
        let reached = dispatch_rows(&mut domain, &plan, [row]);
        assert!(!reached.pending);
        assert_eq!(reached.outcomes.len(), 2);
        for (outcome, row) in reached.outcomes {
            assert_eq!(row.substitution.arguments, vec![value.clone()]);
            let expected = if plan.outcome(outcome).unwrap().body_id == 0 {
                left
            } else {
                right
            };
            assert_eq!(row.constraints, vec![Some(expected)]);
        }
    }

    #[derive(Clone, PartialEq, Eq, Hash)]
    enum BoundRow {
        Choice,
        Producer(usize, ReachabilityState),
    }

    struct BoundRows<'a> {
        concrete: ConcreteDispatchRows<'a>,
        producers: Vec<ReachabilityState>,
        pending: bool,
    }

    impl DispatchRowDomain for BoundRows<'_> {
        type Row = BoundRow;

        fn refine(
            &mut self,
            plan: &PatternDispatchPlan<Ty>,
            row: &BoundRow,
            proof: &Proof<Ty>,
        ) -> RefinedRows<BoundRow> {
            let (producers, pending) = match row {
                BoundRow::Choice => (
                    self.producers.iter().cloned().enumerate().collect::<Vec<_>>(),
                    self.pending,
                ),
                BoundRow::Producer(producer, row) => (vec![(*producer, row.clone())], false),
            };
            RefinedRows {
                rows: producers
                    .into_iter()
                    .flat_map(|(producer, row)| {
                        self.concrete
                            .refine(plan, &row, proof)
                            .rows
                            .into_iter()
                            .map(move |row| BoundRow::Producer(producer, row))
                    })
                    .collect(),
                pending,
            }
        }
    }

    #[test]
    fn shared_dispatch_keeps_joint_producer_rows_and_pending_alternatives() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            2,
            vec![
                row2(Pattern::Atom("a".into()), Pattern::Atom("b".into()), 0),
                row2(Pattern::Atom("b".into()), Pattern::Atom("a".into()), 1),
                row2(Pattern::Wildcard, Pattern::Wildcard, 2),
            ],
        ))
        .unwrap();
        let mut types = Types::new();
        let a = types.atom_lit("a");
        let b = types.atom_lit("b");
        let producers = [vec![a, b], vec![b, a]]
            .into_iter()
            .map(|roots| ReachabilityState {
                roots,
                list_shapes: vec![None; plan.graph.subjects.len()],
            })
            .collect();
        // The test domain names complete producer rows and delegates each
        // actual predicate to the existing concrete restriction operation.
        let mut domain = BoundRows {
            concrete: ConcreteDispatchRows { types: &mut types },
            producers,
            pending: true,
        };
        let result = dispatch_rows(&mut domain, &plan, [BoundRow::Choice]);
        assert!(result.pending, "an unresolved producer must survive beside known rows");
        assert!(!result.fail_reachable);
        assert_eq!(result.outcomes.len(), 2);
        for (outcome, row) in result.outcomes {
            let BoundRow::Producer(producer, row) = row else {
                panic!("the choice must have been restricted")
            };
            assert_eq!(plan.outcome(outcome).unwrap().body_id as usize, producer);
            assert_eq!(row.roots, if producer == 0 { vec![a, b] } else { vec![b, a] });
        }
        domain.producers.clear();
        let pending = dispatch_rows(&mut domain, &plan, [BoundRow::Choice]);
        assert!(pending.pending);
        assert!(pending.outcomes.is_empty());
        assert!(!pending.fail_reachable);
        domain.pending = false;
        let impossible = dispatch_rows(&mut domain, &plan, [BoundRow::Choice]);
        assert!(!impossible.pending);
        assert!(impossible.outcomes.is_empty());
        assert!(!impossible.fail_reachable);
    }

    #[test]
    fn shared_dispatch_memoizes_the_graph_node_with_its_whole_row() {
        struct IdentityRows;
        impl DispatchRowDomain for IdentityRows {
            type Row = u8;
            fn refine(&mut self, _plan: &PatternDispatchPlan<Ty>, row: &u8, _proof: &Proof<Ty>) -> RefinedRows<u8> {
                RefinedRows {
                    rows: vec![*row],
                    pending: false,
                }
            }
        }
        let mut plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![row(Pattern::Atom("a".into()), 0), row(Pattern::Wildcard, 1)],
        ))
        .unwrap();
        let root = plan.graph.root;
        let DispatchNode::Test { on_match, .. } = &mut plan.graph.nodes[root.0 as usize] else {
            panic!("the atom question must lead the test plan")
        };
        on_match.target = root;
        let once = dispatch_rows(&mut IdentityRows, &plan, [7]);
        let repeated = dispatch_rows(&mut IdentityRows, &plan, [7, 7]);
        assert!(once.visited_states <= plan.graph.nodes.len());
        assert_eq!(once.visited_states, repeated.visited_states);
        assert_eq!(once.outcomes, repeated.outcomes);
        assert!(
            !once.outcomes.is_empty(),
            "closing one edge must not discard its sibling"
        );
        let distinct = dispatch_rows(&mut IdentityRows, &plan, [7, 8]);
        assert_eq!(distinct.visited_states, 2 * once.visited_states);
        assert_eq!(distinct.outcomes.len(), 2 * once.outcomes.len());
    }

    /// A guard uses a carrier subject to enter the graph, but that carrier is
    /// not necessarily a runtime read. Its leaves are the authority for which
    /// roots reachability may envelope.
    #[test]
    fn a_guard_envelopes_only_the_input_its_leaves_read() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            3,
            vec![
                PatternRow {
                    patterns: vec![
                        Spanned::dummy(Pattern::Var("first".to_string())),
                        Spanned::dummy(Pattern::Var("second".to_string())),
                        Spanned::dummy(Pattern::Var("tested".to_string())),
                    ],
                    preconditions: Vec::new(),
                    guard: Some(Spanned::dummy(Expr::Var("tested".to_string()))),
                    body_id: 0,
                },
                PatternRow {
                    patterns: vec![
                        Spanned::dummy(Pattern::Wildcard),
                        Spanned::dummy(Pattern::Wildcard),
                        Spanned::dummy(Pattern::Wildcard),
                    ],
                    preconditions: Vec::new(),
                    guard: None,
                    body_id: 1,
                },
            ],
        ))
        .expect("the guard reads its third input");
        assert_eq!(
            plan.input_demand(),
            [DispatchDemand::Ignore, DispatchDemand::Ignore, DispatchDemand::Whole],
            "the plan, not reachability, records the guard's exact input read"
        );

        let mut types = Types::new();
        let first = types.type_var(TypeVarId(40));
        let second = types.type_var(TypeVarId(41));
        let tested = types.type_var(TypeVarId(42));
        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[first, second, tested]);
        let any = types.any();

        assert_eq!(
            reachable_body_ids(&plan, &reachability),
            vec![0, 1],
            "the guard and fallback both remain reachable"
        );
        for (outcome, inputs) in &reachability.outcome_inputs {
            assert_eq!(
                inputs[0], first,
                "outcome {outcome:?} must retain its first untouched variable"
            );
            assert_eq!(
                inputs[1], second,
                "outcome {outcome:?} must retain its second untouched variable"
            );
            assert!(
                types.is_equivalent(&inputs[2], &any),
                "outcome {outcome:?} must envelope only the guard's third input"
            );
        }
    }

    fn reachable_body_ids(plan: &PatternDispatchPlan<Ty>, reachability: &DispatchReachability) -> Vec<u32> {
        plan.outcomes
            .iter()
            .enumerate()
            .filter(|(index, _)| reachability.outcomes.binary_search(&OutcomeId(*index as u32)).is_ok())
            .map(|(_, outcome)| outcome.body_id)
            .collect()
    }

    #[test]
    fn named_struct_field_constraints_refine_their_exact_root_and_reject_other_families() {
        use crate::compiler2::dispatch::SourcePatternResolver;
        use crate::compiler2::{ModuleId, Namespace, World};
        use crate::dispatch_matrix::pattern::pattern_dispatch_from_source_with_resolver;
        use crate::modules::identity::ModuleName;

        let mut world = World::new();
        let name = ModuleName::parse_dotted("Nested.Box").unwrap();
        let module = world.reference_module(name.clone());
        let other_module = world.reference_module(ModuleName::parse_dotted("Other.Box").unwrap());
        let mut resolver = SourcePatternResolver {
            world: &mut world,
            namespace: Namespace::default(),
            owner: ModuleId::GLOBAL,
            guard: |_world: &mut World, _callee: &crate::ast::Callee, _arity: usize| Ok(None),
        };
        let plan = pattern_dispatch_from_source_with_resolver(
            SourcePatternRows::lexical(
                1,
                vec![
                    row(
                        Pattern::Tuple(vec![Spanned::dummy(Pattern::Struct {
                            module: crate::ast::ModuleTarget::Unresolved(name),
                            fields: vec![("value".into(), Spanned::dummy(Pattern::Atom("hit".into())))],
                        })]),
                        0,
                    ),
                    row(Pattern::Wildcard, 1),
                ],
            ),
            &mut resolver,
        )
        .unwrap();
        let hit = world.types_mut().atom_lit("hit");
        let miss = world.types_mut().atom_lit("miss");
        let values = world.types_mut().union(hit, miss);
        let fields = vec!["value".into()];
        let named = world.struct_value_ty(module, &fields, &[values]);
        let named_hit = world.struct_value_ty(module, &fields, &[hit]);
        let named_miss = world.struct_value_ty(module, &fields, &[miss]);
        let wrong = world.struct_value_ty(other_module, &fields, &[hit]);
        let plain = world.types_mut().map(&[(MapKey::Atom("value".into()), hit)]);
        let types = world.types_mut();
        for (input, expected) in [
            (named_hit, vec![0]),
            (named_miss, vec![1]),
            (wrong, vec![1]),
            (plain, vec![1]),
        ] {
            let input = types.tuple(&[input]);
            let reach = calculate_dispatch_reachability(types, &plan, &[input]);
            assert_eq!(reachable_body_ids(&plan, &reach), expected);
            assert!(!reach.fail_reachable);
        }
        let input = types.tuple(&[named]);
        let reach = calculate_dispatch_reachability(types, &plan, &[input]);
        assert_eq!(reachable_body_ids(&plan, &reach), vec![0, 1]);
        let matched_root = reach
            .outcome_inputs
            .iter()
            .find(|(outcome, _)| *outcome == OutcomeId(0))
            .unwrap()
            .1[0];
        let expected = types.tuple(&[named_hit]);
        assert!(
            types.is_equivalent(&matched_root, &expected),
            "field evidence must lift through the enclosing tuple without losing its struct tag"
        );
    }

    fn list_pattern(length: usize, open_tail: bool) -> Pattern {
        Pattern::List(
            (0..length).map(|_| Spanned::dummy(Pattern::Wildcard)).collect(),
            open_tail.then(|| Box::new(Spanned::dummy(Pattern::Wildcard))),
        )
    }

    #[test]
    fn proper_list_domain_is_exhausted_by_zero_one_and_two_plus_rows() {
        let total = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![
                row(list_pattern(0, false), 0),
                row(list_pattern(1, false), 1),
                row(list_pattern(2, true), 2),
            ],
        ))
        .expect("list length partitions should compile");
        let partial = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![row(list_pattern(0, false), 0), row(list_pattern(2, true), 1)],
        ))
        .expect("partial list length partitions should compile");
        let mut types = Types::new();
        let any = types.any();
        let input = types.list(any);

        let total_reachability = calculate_dispatch_reachability(&mut types, &total, &[input]);
        let partial_reachability = calculate_dispatch_reachability(&mut types, &partial, &[input]);
        let unconstrained_reachability = calculate_dispatch_reachability(&mut types, &total, &[any]);

        assert_eq!(reachable_body_ids(&total, &total_reachability), vec![0, 1, 2]);
        assert!(!total_reachability.fail_reachable);
        assert!(partial_reachability.fail_reachable);
        assert!(
            unconstrained_reachability.fail_reachable,
            "the list partition must not consume non-list values"
        );
    }

    #[test]
    fn bare_template_inputs_are_refined_as_runtime_values() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![row(Pattern::Atom("x".to_string()), 0), row(Pattern::Wildcard, 1)],
        ))
        .expect("atom patterns should compile");
        let mut types = Types::new();
        let input = types.type_var(TypeVarId(0));

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
        let atom_input = reachability
            .outcome_inputs
            .iter()
            .find_map(|(outcome, inputs)| (plan.outcome(*outcome)?.body_id == 0).then_some(inputs[0]))
            .expect("the atom outcome should retain its refined input");
        let x = types.atom_lit("x");
        assert!(types.is_equivalent(&atom_input, &x));
    }

    #[test]
    fn nested_template_inputs_keep_their_runtime_structure() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![
                row(
                    Pattern::Tuple(vec![
                        Spanned::dummy(Pattern::Atom("x".to_string())),
                        Spanned::dummy(Pattern::Wildcard),
                    ]),
                    0,
                ),
                row(Pattern::Wildcard, 1),
            ],
        ))
        .expect("tuple patterns should compile");
        let mut types = Types::new();
        let alpha = types.type_var(TypeVarId(0));
        let beta = types.type_var(TypeVarId(1));
        let input = types.tuple(&[alpha, beta]);

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
        let refined = reachability
            .outcome_inputs
            .iter()
            .find_map(|(outcome, inputs)| (plan.outcome(*outcome)?.body_id == 0).then_some(inputs[0]))
            .expect("the tuple outcome should retain its refined input");
        assert_eq!(types.max_tuple_arity(&refined), 2);
        assert!(!types.has_vars(&refined));
    }

    #[test]
    fn nested_positive_runtime_envelope_grounds_projectable_structures() {
        let mut types = Types::new();
        let alpha = types.type_var(TypeVarId(0));
        let list = types.list(alpha);
        let map = types.map(&[(MapKey::Atom("items".to_string()), list)]);
        let input = types.tuple(&[map]);
        let envelope = types.runtime_envelope(input);
        let any = types.any();
        let list = types.list(any);
        let map = types.map(&[(MapKey::Atom("items".to_string()), list)]);
        let expected = types.tuple(&[map]);

        assert!(types.is_equivalent(&envelope, &expected));
        assert!(!types.has_vars(&envelope));
    }

    #[test]
    fn callable_template_inputs_keep_their_callable_correlation() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(1, vec![row(Pattern::Wildcard, 0)]))
            .expect("wildcard patterns should compile");
        let mut types = Types::new();
        let input = types.closure_lit(crate::compiler2::types::ClosureTarget(7), Vec::new(), 2);

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0]);
        assert!(types.is_equivalent(&reachability.outcome_inputs[0].1[0], &input));
    }

    #[test]
    fn ground_dispatch_inputs_are_unchanged() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![row(Pattern::Atom("x".to_string()), 0), row(Pattern::Wildcard, 1)],
        ))
        .expect("atom patterns should compile");
        let mut types = Types::new();
        let input = types.atom_lit("x");

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0]);
        assert!(types.is_equivalent(&reachability.outcome_inputs[0].1[0], &input));
    }

    #[test]
    fn symbolic_wide_tuple_decision_chain_stays_graph_bounded() {
        let width = 16;
        let mut rows = (0..width)
            .map(|index| {
                let mut fields = (0..width)
                    .map(|_| Spanned::dummy(Pattern::Wildcard))
                    .collect::<Vec<_>>();
                fields[index] = Spanned::dummy(Pattern::Bool(true));
                row(Pattern::Tuple(fields), index as u32)
            })
            .collect::<Vec<_>>();
        rows.push(row(
            Pattern::Tuple((0..width).map(|_| Spanned::dummy(Pattern::Wildcard)).collect()),
            width as u32,
        ));
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(1, rows))
            .expect("wide tuple patterns should compile through the production pattern builder");
        let mut types = Types::new();
        let boolean = types.bool();
        let fields = types.repeat(boolean, width);
        let input = types.tuple(&fields);

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(
            reachable_body_ids(&plan, &reachability),
            (0..=width as u32).collect::<Vec<_>>()
        );
        assert!(!reachability.fail_reachable);
        assert!(
            reachability.visited_states <= width * 8,
            "symbolic traversal visited {} states",
            reachability.visited_states,
        );
        assert_eq!(reachability.max_root_slots, plan.input_count);
        assert!(plan.graph.subjects.len() > reachability.max_root_slots);
    }

    #[test]
    fn negative_tuple_conjunction_remains_a_conservative_root_alternative() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![
                row(
                    Pattern::Tuple(vec![
                        Spanned::dummy(Pattern::Atom("a".to_string())),
                        Spanned::dummy(Pattern::Wildcard),
                    ]),
                    0,
                ),
                row(Pattern::Wildcard, 1),
            ],
        ))
        .expect("tuple patterns should compile");
        let mut types = Types::new();
        let atom = types.atom();
        let any_pair = types.tuple(&[atom, atom]);
        let a = types.atom_lit("a");
        let any = types.any();
        let excluded = types.tuple(&[a, any]);
        let input = types.difference(any_pair, excluded);

        assert_eq!(types.projection_alternatives(input), vec![input]);

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert!(reachable_body_ids(&plan, &reachability).contains(&1));
        assert!(!reachability.fail_reachable);
        assert_eq!(reachability.max_root_slots, plan.input_count);
    }

    #[test]
    fn unresolved_negative_tuple_exclusion_keeps_both_dispatch_rows_reachable() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![
                row(
                    Pattern::Tuple(vec![
                        Spanned::dummy(Pattern::Atom("a".to_string())),
                        Spanned::dummy(Pattern::Wildcard),
                    ]),
                    0,
                ),
                row(Pattern::Wildcard, 1),
            ],
        ))
        .expect("tuple patterns should compile");
        let mut types = Types::new();
        let any = types.any();
        let universe = types.tuple(&[any, any]);
        let a = types.atom_lit("a");
        let alpha = types.type_var(TypeVarId(0));
        let excluded = types.tuple(&[a, alpha]);
        let input = types.difference(universe, excluded);

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
        assert!(!reachability.fail_reachable);
    }

    #[test]
    fn mixed_runtime_envelope_keeps_the_grounded_part_of_an_exclusion() {
        let mut types = Types::new();
        let any = types.any();
        let alpha = types.type_var(TypeVarId(0));
        let lists = types.list(any);
        let alpha_lists = types.list(alpha);
        let non_alpha_lists = types.difference(lists, alpha_lists);
        let map = types.map(&[(MapKey::Atom("items".to_string()), non_alpha_lists)]);
        let input = types.tuple(&[map]);
        let envelope = types.runtime_envelope(input);
        let non_empty_lists = types.non_empty_list(any);
        let map = types.map(&[(MapKey::Atom("items".to_string()), non_empty_lists)]);
        let expected = types.tuple(&[map]);

        assert!(types.is_equivalent(&envelope, &expected));
        assert!(!types.has_vars(&envelope));
    }

    #[test]
    fn positive_resource_envelope_grounds_its_payload() {
        let mut types = Types::new();
        let alpha = types.type_var(TypeVarId(0));
        let input = types.resource(alpha);
        let envelope = types.runtime_envelope(input);
        let any = types.any();
        let expected = types.resource(any);

        assert!(types.is_equivalent(&envelope, &expected));
        assert!(!types.has_vars(&envelope));
    }

    #[test]
    fn nested_resource_envelope_grounds_every_inspectable_payload() {
        let mut types = Types::new();
        let alpha = types.type_var(TypeVarId(0));
        let inner = types.resource(alpha);
        let input = types.resource(inner);
        let envelope = types.runtime_envelope(input);
        let any = types.any();
        let inner = types.resource(any);
        let expected = types.resource(inner);

        assert!(types.is_equivalent(&envelope, &expected));
        assert!(!types.has_vars(&envelope));
    }

    #[test]
    fn negative_resource_envelope_does_not_widen_its_exclusion() {
        let mut types = Types::new();
        let any = types.any();
        let resources = types.resource(any);
        let alpha = types.type_var(TypeVarId(0));
        let alpha_resources = types.resource(alpha);
        let input = types.difference(resources, alpha_resources);
        let envelope = types.runtime_envelope(input);

        assert!(types.is_equivalent(&envelope, &resources));
        assert!(!types.has_vars(&envelope));
    }

    #[test]
    fn resource_envelopes_contain_representative_concrete_instantiations() {
        let mut types = Types::new();
        let alpha_id = TypeVarId(0);
        let alpha = types.type_var(alpha_id);
        let resource = types.resource(alpha);
        let nested = types.resource(resource);
        let any = types.any();
        let resources = types.resource(any);
        let excluded = types.difference(resources, resource);
        let templates = [resource, nested, excluded];
        let envelopes = templates.map(|template| types.runtime_envelope(template));
        let int = types.int();
        let atom = types.atom();
        let list = types.list(int);

        for witness in [int, atom, list] {
            let mut sigma = Sigma::new();
            sigma.insert(alpha_id, witness);
            for (template, envelope) in templates.iter().zip(envelopes.iter()) {
                let instantiated = types.instantiate(template, &sigma);
                assert!(types.is_subtype(&instantiated, envelope));
            }
        }
    }

    #[test]
    fn cofinite_variable_double_negation_preserves_possible_tuple_values() {
        let mut types = Types::new();
        let alpha = types.type_var(TypeVarId(0));
        let any = types.any();
        let not_alpha = types.difference(any, alpha);
        let universe = types.tuple(&[any]);
        let excluded = types.tuple(&[not_alpha]);
        let input = types.difference(universe, excluded);
        let envelope = types.runtime_envelope(input);

        assert!(types.is_equivalent(&envelope, &universe));
        assert!(!types.is_empty(&envelope));
    }

    #[test]
    fn finite_negative_variable_branch_preserves_mixed_ground_axes() {
        let mut types = Types::new();
        let alpha = types.type_var(TypeVarId(0));
        let int = types.int();
        let alpha_or_int = types.union(alpha, int);
        let any = types.any();
        let universe = types.tuple(&[any]);
        let excluded = types.tuple(&[alpha_or_int]);
        let input = types.difference(universe, excluded);
        let envelope = types.runtime_envelope(input);
        let excluded = types.tuple(&[int]);
        let expected = types.difference(universe, excluded);

        assert!(types.is_equivalent(&envelope, &expected));
    }

    #[test]
    fn positive_cofinite_variable_branch_remains_a_runtime_top() {
        let mut types = Types::new();
        let alpha = types.type_var(TypeVarId(0));
        let any = types.any();
        let not_alpha = types.difference(any, alpha);
        let envelope = types.runtime_envelope(not_alpha);

        assert!(types.is_equivalent(&envelope, &any));
    }

    #[test]
    fn saturated_variable_axis_without_exclusions_remains_ordinary_top() {
        let mut types = Types::new();
        let any = types.any();
        let universe = types.tuple(&[any]);
        let input = types.difference(universe, universe);
        let envelope = types.runtime_envelope(input);

        assert!(types.is_empty(&envelope));
    }

    #[test]
    fn cofinite_variable_double_negation_preserves_possible_resource_values() {
        let mut types = Types::new();
        let alpha = types.type_var(TypeVarId(0));
        let any = types.any();
        let not_alpha = types.difference(any, alpha);
        let resources = types.resource(any);
        let excluded = types.resource(not_alpha);
        let input = types.difference(resources, excluded);
        let envelope = types.runtime_envelope(input);

        assert!(types.is_equivalent(&envelope, &resources));
        assert!(!types.is_empty(&envelope));
    }

    #[test]
    fn cofinite_double_negation_envelopes_contain_concrete_instantiations() {
        let mut types = Types::new();
        let alpha_id = TypeVarId(0);
        let alpha = types.type_var(alpha_id);
        let any = types.any();
        let not_alpha = types.difference(any, alpha);
        let tuple_universe = types.tuple(&[any]);
        let tuple_excluded = types.tuple(&[not_alpha]);
        let tuple_template = types.difference(tuple_universe, tuple_excluded);
        let resource_universe = types.resource(any);
        let resource_excluded = types.resource(not_alpha);
        let resource_template = types.difference(resource_universe, resource_excluded);
        let templates = [tuple_template, resource_template];
        let envelopes = templates.map(|template| types.runtime_envelope(template));
        let int = types.int();
        let atom = types.atom();
        let list = types.list(int);

        for witness in [int, atom, list] {
            let mut sigma = Sigma::new();
            sigma.insert(alpha_id, witness);
            for (template, envelope) in templates.iter().zip(envelopes.iter()) {
                let instantiated = types.instantiate(template, &sigma);
                assert!(types.is_subtype(&instantiated, envelope));
            }
        }
    }

    #[test]
    fn unresolved_resource_payload_keeps_matching_type_precondition_reachable() {
        let mut types = Types::new();
        let int = types.int();
        let resource_int = types.resource(int);
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![
                PatternRow {
                    patterns: vec![Spanned::dummy(Pattern::Wildcard)],
                    preconditions: vec![(PatternSubjectRef::Input(0), resource_int)],
                    guard: None,
                    body_id: 0,
                },
                row(Pattern::Wildcard, 1),
            ],
        ))
        .expect("resource preconditions should compile");
        let alpha = types.type_var(TypeVarId(0));
        let input = types.resource(alpha);

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
        assert!(!reachability.fail_reachable);
    }

    #[test]
    fn mixed_axis_union_remains_conservative_through_tuple_projection() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            1,
            vec![
                row(
                    Pattern::Tuple(vec![
                        Spanned::dummy(Pattern::Atom("a".to_string())),
                        Spanned::dummy(Pattern::Atom("x".to_string())),
                    ]),
                    0,
                ),
                row(Pattern::Wildcard, 1),
            ],
        ))
        .expect("tuple patterns should compile");
        let mut types = Types::new();
        let a = types.atom_lit("a");
        let x = types.atom_lit("x");
        let pair = types.tuple(&[a, x]);
        let other = types.atom_lit("other");
        let input = types.union(pair, other);

        assert_eq!(types.projection_alternatives(input), vec![input]);

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
        assert!(!reachability.fail_reachable);
        assert_eq!(reachability.max_root_slots, plan.input_count);
    }

    /// fz-f98.14.11 — a slot no test looks at comes back exactly as it went
    /// in. The runtime envelope answers "what could this be at runtime", which
    /// is `any` for a type variable, and that is right for deciding which
    /// clauses a value can reach. But the refined inputs are also what types
    /// the clause's parameters, and there a variable means NOT-YET-KNOWN, not
    /// "anything" -- graduating it to `any` there loses the binding the
    /// fixpoint is still working out, and cumulative joins never take it back.
    /// A slot that appears in no test cannot change any test's outcome, so it
    /// needs no envelope at all.
    #[test]
    fn a_slot_no_test_looks_at_keeps_its_type_variable() {
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
            2,
            vec![
                row2(Pattern::Atom("x".to_string()), Pattern::Wildcard, 0),
                row2(Pattern::Wildcard, Pattern::Wildcard, 1),
            ],
        ))
        .expect("atom patterns should compile");
        let mut types = Types::new();
        let tested = types.type_var(TypeVarId(0));
        let untested = types.type_var(TypeVarId(1));

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[tested, untested]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
        assert!(
            !reachability.outcome_inputs.is_empty(),
            "both clauses should be reachable with refined inputs"
        );
        let any = types.any();
        for (outcome, inputs) in &reachability.outcome_inputs {
            assert_eq!(
                inputs[1],
                untested,
                "outcome {outcome:?}: the untested slot should keep its variable, got `{}`",
                types.display(&inputs[1])
            );
            assert!(
                !types.is_equivalent(&inputs[1], &any),
                "outcome {outcome:?}: the untested slot must not graduate to any"
            );
        }
    }

    #[test]
    fn nil_predicates_use_the_atom_type_and_map_key() {
        let mut types = Types::new();
        let nil = predicate_target(&mut types, &Region::Equal(ComparisonValue::Const(GroundValue::Nil)))
            .expect("nil equality is type-representable");
        assert!(types.is_nil(&nil.ty));

        let required = predicate_target(&mut types, &Region::MapKeyPresent { key: GroundValue::Nil })
            .expect("nil is the atom key :nil");
        let any = types.any();
        let expected = types.map(&[(crate::ground_value::MapKey::Atom("nil".to_string()), any)]);
        assert!(types.is_equivalent(&required.ty, &expected));
    }
}
