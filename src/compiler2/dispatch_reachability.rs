use std::collections::{BTreeSet, HashSet};

use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::dispatch_matrix::{
    BitstringFieldKind, ComparisonValue, DispatchNode, GraphNodeId, ListRegion, OutcomeId, ProjectionKind, ProofSense,
    Region, RegionPredicate, SubjectId, SubjectSource,
};
use crate::ground_value::{DispatchShape, GroundValue};

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
    let mut calculator = ReachabilityCalculator {
        types,
        plan,
        visited: HashSet::new(),
        outcomes: BTreeSet::new(),
        outcome_inputs: BTreeSet::new(),
        fail_reachable: false,
        #[cfg(test)]
        max_root_slots: 0,
    };
    let list_shapes = vec![None; plan.graph.subjects.len()];
    calculator.visit(plan.graph.root, ReachabilityState { roots, list_shapes });
    DispatchReachability {
        outcomes: calculator.outcomes.into_iter().collect(),
        outcome_inputs: calculator.outcome_inputs.into_iter().collect(),
        fail_reachable: calculator.fail_reachable,
        #[cfg(test)]
        visited_states: calculator.visited.len(),
        #[cfg(test)]
        max_root_slots: calculator.max_root_slots,
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ReachabilityState {
    roots: Vec<Ty>,
    list_shapes: Vec<Option<ListRegion>>,
}

struct ReachabilityCalculator<'a> {
    types: &'a mut Types,
    plan: &'a PatternDispatchPlan<Ty>,
    visited: HashSet<(GraphNodeId, ReachabilityState)>,
    outcomes: BTreeSet<OutcomeId>,
    outcome_inputs: BTreeSet<(OutcomeId, Vec<Ty>)>,
    fail_reachable: bool,
    #[cfg(test)]
    max_root_slots: usize,
}

impl ReachabilityCalculator<'_> {
    fn visit(&mut self, node_id: GraphNodeId, state: ReachabilityState) {
        #[cfg(test)]
        {
            self.max_root_slots = self.max_root_slots.max(state.roots.len());
        }
        if !self.visited.insert((node_id, state.clone())) {
            return;
        }
        let Some(node) = self.plan.graph.node(node_id) else {
            return;
        };
        match node {
            DispatchNode::Fail => self.fail_reachable = true,
            DispatchNode::Outcome { outcome, .. } => {
                self.outcomes.insert(*outcome);
                self.outcome_inputs.insert((*outcome, state.roots));
            }
            DispatchNode::Test { on_match, on_miss, .. } => {
                if let Some(next) = self.apply_proofs(&state, &on_match.evidence.proofs) {
                    self.visit(on_match.target, next);
                }
                if let Some(next) = self.apply_proofs(&state, &on_miss.evidence.proofs) {
                    self.visit(on_miss.target, next);
                }
            }
        }
    }

    fn apply_proofs(
        &mut self,
        state: &ReachabilityState,
        proofs: &[crate::dispatch_matrix::Proof<Ty>],
    ) -> Option<ReachabilityState> {
        let mut refined = state.clone();
        for proof in proofs {
            refined = self.apply_proof(refined, &proof.predicate, proof.sense)?;
        }
        Some(refined)
    }

    fn apply_proof(
        &mut self,
        mut state: ReachabilityState,
        predicate: &RegionPredicate<Ty>,
        sense: ProofSense,
    ) -> Option<ReachabilityState> {
        let subject = predicate.subject;
        self.record_list_shape(&state.roots, &mut state.list_shapes, predicate, subject, sense)?;
        let Some(target) = predicate_target(self.types, &predicate.region) else {
            return Some(state);
        };
        let ordinal = subject_input(self.plan, subject)?;
        let root = *state.roots.get(ordinal)?;
        let alternatives = self.types.projection_alternatives(root);
        let mut matched = None;
        let mut missed = None;
        for alternative in alternatives {
            let mut row = state.roots.clone();
            row[ordinal] = alternative;
            let projected = project_subject(self.types, self.plan, &row, subject);
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
                && exact_projection_path(self.plan, subject)
                && let Some((lifted_ordinal, lifted)) =
                    lift_projection_constraint(self.types, self.plan, &row, subject, target.ty)
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
                let projected = project_subject(self.types, self.plan, roots, subject);
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
#[path = "dispatch_reachability_test.rs"]
mod dispatch_reachability_test;
