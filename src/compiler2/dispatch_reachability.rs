use std::collections::{BTreeSet, HashSet};

use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternSubjectRef};
use crate::dispatch_matrix::{
    ComparisonValue, DispatchNode, GraphNodeId, ListRegion, OutcomeId, ProofSense, Region, RegionPredicate,
};
use crate::ground_value::{DispatchShape, GroundValue};

use super::types::{Ty, Types};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DispatchReachability {
    pub(crate) outcomes: Vec<OutcomeId>,
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
    let roots = (0..plan.input_count)
        .map(|ordinal| inputs.get(ordinal).copied().unwrap_or(any))
        .collect::<Vec<_>>();
    let mut calculator = ReachabilityCalculator {
        types,
        plan,
        visited: HashSet::new(),
        outcomes: BTreeSet::new(),
        fail_reachable: false,
        #[cfg(test)]
        max_root_slots: 0,
    };
    calculator.visit(plan.graph.root, roots);
    DispatchReachability {
        outcomes: calculator.outcomes.into_iter().collect(),
        fail_reachable: calculator.fail_reachable,
        #[cfg(test)]
        visited_states: calculator.visited.len(),
        #[cfg(test)]
        max_root_slots: calculator.max_root_slots,
    }
}

struct ReachabilityCalculator<'a> {
    types: &'a mut Types,
    plan: &'a PatternDispatchPlan<Ty>,
    visited: HashSet<(GraphNodeId, Vec<Ty>)>,
    outcomes: BTreeSet<OutcomeId>,
    fail_reachable: bool,
    #[cfg(test)]
    max_root_slots: usize,
}

impl ReachabilityCalculator<'_> {
    fn visit(&mut self, node_id: GraphNodeId, roots: Vec<Ty>) {
        #[cfg(test)]
        {
            self.max_root_slots = self.max_root_slots.max(roots.len());
        }
        if !self.visited.insert((node_id, roots.clone())) {
            return;
        }
        let Some(node) = self.plan.graph.node(node_id) else {
            return;
        };
        match node {
            DispatchNode::Fail => self.fail_reachable = true,
            DispatchNode::Outcome { outcome, .. } => {
                self.outcomes.insert(*outcome);
            }
            DispatchNode::Test { on_match, on_miss, .. } => {
                if let Some(next) = self.apply_proofs(&roots, &on_match.evidence.proofs) {
                    self.visit(on_match.target, next);
                }
                if let Some(next) = self.apply_proofs(&roots, &on_miss.evidence.proofs) {
                    self.visit(on_miss.target, next);
                }
            }
        }
    }

    fn apply_proofs(&mut self, roots: &[Ty], proofs: &[crate::dispatch_matrix::Proof<Ty>]) -> Option<Vec<Ty>> {
        let mut refined = roots.to_vec();
        for proof in proofs {
            refined = self.apply_proof(&refined, &proof.predicate, proof.sense)?;
        }
        Some(refined)
    }

    fn apply_proof(&mut self, roots: &[Ty], predicate: &RegionPredicate<Ty>, sense: ProofSense) -> Option<Vec<Ty>> {
        let Some(subject) = self.plan.subject_ref(predicate.subject) else {
            return Some(roots.to_vec());
        };
        let Some(target) = predicate_target(self.types, &predicate.region) else {
            return Some(roots.to_vec());
        };
        let ordinal = subject_input(subject)?;
        let root = *roots.get(ordinal)?;
        let alternatives = self.types.projection_alternatives(root);
        let mut matched = None;
        let mut missed = None;
        for alternative in alternatives {
            let mut row = roots.to_vec();
            row[ordinal] = alternative;
            let projected = project_subject(self.types, &row, subject);
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
                && tuple_only_path(subject)
                && let Some((lifted_ordinal, lifted)) = lift_tuple_constraint(self.types, &row, subject, target.ty)
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
        let mut refined = roots.to_vec();
        refined[ordinal] = selected;
        Some(refined)
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

fn subject_input(subject: &PatternSubjectRef) -> Option<usize> {
    match subject {
        PatternSubjectRef::Input(ordinal) => Some(*ordinal as usize),
        PatternSubjectRef::TupleField { tuple, .. } => subject_input(tuple),
        PatternSubjectRef::ListHead(list) | PatternSubjectRef::ListTail(list) => subject_input(list),
        PatternSubjectRef::MapValue { map, .. } => subject_input(map),
        PatternSubjectRef::BitstringField { bitstring, .. } => subject_input(bitstring),
    }
}

fn tuple_only_path(subject: &PatternSubjectRef) -> bool {
    match subject {
        PatternSubjectRef::Input(_) => true,
        PatternSubjectRef::TupleField { tuple, .. } => tuple_only_path(tuple),
        PatternSubjectRef::ListHead(_)
        | PatternSubjectRef::ListTail(_)
        | PatternSubjectRef::MapValue { .. }
        | PatternSubjectRef::BitstringField { .. } => false,
    }
}

fn project_subject(types: &mut Types, roots: &[Ty], subject: &PatternSubjectRef) -> Ty {
    match subject {
        PatternSubjectRef::Input(ordinal) => roots.get(*ordinal as usize).copied().unwrap_or_else(|| types.any()),
        PatternSubjectRef::TupleField { tuple, index } => {
            let tuple = project_subject(types, roots, tuple);
            types.tuple_field_type(&tuple, *index as usize)
        }
        PatternSubjectRef::ListHead(list) => {
            let list = project_subject(types, roots, list);
            types.list_element_type(&list)
        }
        PatternSubjectRef::ListTail(list) => {
            let list = project_subject(types, roots, list);
            let element = types.list_element_type(&list);
            types.list(element)
        }
        PatternSubjectRef::MapValue { .. } | PatternSubjectRef::BitstringField { .. } => types.any(),
    }
}

fn lift_tuple_constraint(
    types: &mut Types,
    roots: &[Ty],
    subject: &PatternSubjectRef,
    constraint: Ty,
) -> Option<(usize, Ty)> {
    match subject {
        PatternSubjectRef::Input(ordinal) => Some((*ordinal as usize, constraint)),
        PatternSubjectRef::TupleField { tuple, index } => {
            let tuple_ty = project_subject(types, roots, tuple);
            let arity = types.max_tuple_arity(&tuple_ty);
            if *index as usize >= arity {
                return None;
            }
            let any = types.any();
            let mut fields = types.repeat(any, arity);
            fields[*index as usize] = constraint;
            let tuple_constraint = types.tuple(&fields);
            lift_tuple_constraint(types, roots, tuple, tuple_constraint)
        }
        PatternSubjectRef::ListHead(_)
        | PatternSubjectRef::ListTail(_)
        | PatternSubjectRef::MapValue { .. }
        | PatternSubjectRef::BitstringField { .. } => None,
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
    use crate::ast::{Pattern, Spanned};
    use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};

    fn row(pattern: Pattern, body_id: u32) -> PatternRow<Ty> {
        PatternRow {
            patterns: vec![Spanned::dummy(pattern)],
            preconditions: Vec::new(),
            guard: None,
            body_id,
        }
    }

    fn reachable_body_ids(plan: &PatternDispatchPlan<Ty>, reachability: &DispatchReachability) -> Vec<u32> {
        plan.outcomes
            .iter()
            .filter(|outcome| reachability.outcomes.binary_search(&outcome.outcome).is_ok())
            .map(|outcome| outcome.body_id)
            .collect()
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
        let plan = pattern_dispatch_from_source(SourcePatternRows { input_count: 1, rows })
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
        assert!(plan.matrix.subjects.len() > reachability.max_root_slots);
    }

    #[test]
    fn negative_tuple_conjunction_remains_a_conservative_root_alternative() {
        let plan = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![
                row(
                    Pattern::Tuple(vec![
                        Spanned::dummy(Pattern::Atom("a".to_string())),
                        Spanned::dummy(Pattern::Wildcard),
                    ]),
                    0,
                ),
                row(Pattern::Wildcard, 1),
            ],
        })
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
    fn mixed_axis_union_remains_conservative_through_tuple_projection() {
        let plan = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![
                row(
                    Pattern::Tuple(vec![
                        Spanned::dummy(Pattern::Atom("a".to_string())),
                        Spanned::dummy(Pattern::Atom("x".to_string())),
                    ]),
                    0,
                ),
                row(Pattern::Wildcard, 1),
            ],
        })
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
