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
    let tested = tested_input_ordinals(plan);
    let roots = (0..plan.input_count)
        .map(|ordinal| {
            let input = inputs.get(ordinal).copied().unwrap_or(any);
            if tested.contains(&ordinal) {
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
    let list_shapes = vec![None; plan.matrix.subjects.len()];
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

/// The input ordinals some test in the plan reads, directly or through a
/// projection. Guards are conservative: a guard's inputs are not modelled
/// here, so every ordinal a guard could observe is treated as tested.
fn tested_input_ordinals(plan: &PatternDispatchPlan<Ty>) -> HashSet<usize> {
    if !plan.guards.is_empty() {
        return (0..plan.input_count).collect();
    }
    plan.graph
        .nodes
        .iter()
        .filter_map(|node| match node {
            DispatchNode::Test { predicate, .. } => subject_input(plan, predicate.subject),
            _ => None,
        })
        .collect()
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
    use crate::ast::{Pattern, Spanned};
    use crate::compiler2::types::{MapKey, Sigma, TypeVarId};
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

    fn reachable_body_ids(plan: &PatternDispatchPlan<Ty>, reachability: &DispatchReachability) -> Vec<u32> {
        plan.outcomes
            .iter()
            .filter(|outcome| reachability.outcomes.binary_search(&outcome.outcome).is_ok())
            .map(|outcome| outcome.body_id)
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
            guard: |_world: &mut World, _name: &crate::ast::CallableName, _arity: usize| Ok(None),
        };
        let plan = pattern_dispatch_from_source_with_resolver(
            SourcePatternRows {
                input_count: 1,
                rows: vec![
                    row(
                        Pattern::Tuple(vec![Spanned::dummy(Pattern::Struct {
                            module: crate::ast::ModuleTarget::Unresolved(name),
                            fields: vec![("value".into(), Spanned::dummy(Pattern::Atom("hit".into())))],
                        })]),
                        0,
                    ),
                    row(Pattern::Wildcard, 1),
                ],
            },
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
            .find(|(outcome, _)| *outcome == plan.outcomes[0].outcome)
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
        let total = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![
                row(list_pattern(0, false), 0),
                row(list_pattern(1, false), 1),
                row(list_pattern(2, true), 2),
            ],
        })
        .expect("list length partitions should compile");
        let partial = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![row(list_pattern(0, false), 0), row(list_pattern(2, true), 1)],
        })
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
        let plan = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![row(Pattern::Atom("x".to_string()), 0), row(Pattern::Wildcard, 1)],
        })
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
        let plan = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![
                row(
                    Pattern::Tuple(vec![
                        Spanned::dummy(Pattern::Atom("x".to_string())),
                        Spanned::dummy(Pattern::Wildcard),
                    ]),
                    0,
                ),
                row(Pattern::Wildcard, 1),
            ],
        })
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
        let plan = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![row(Pattern::Wildcard, 0)],
        })
        .expect("wildcard patterns should compile");
        let mut types = Types::new();
        let input = types.closure_lit(crate::compiler2::types::ClosureTarget(7), Vec::new(), 2);

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0]);
        assert!(types.is_equivalent(&reachability.outcome_inputs[0].1[0], &input));
    }

    #[test]
    fn ground_dispatch_inputs_are_unchanged() {
        let plan = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![row(Pattern::Atom("x".to_string()), 0), row(Pattern::Wildcard, 1)],
        })
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
    fn unresolved_negative_tuple_exclusion_keeps_both_dispatch_rows_reachable() {
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
        let plan = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 1,
            rows: vec![
                PatternRow {
                    patterns: vec![Spanned::dummy(Pattern::Wildcard)],
                    preconditions: vec![(PatternSubjectRef::Input(0), resource_int)],
                    guard: None,
                    body_id: 0,
                },
                row(Pattern::Wildcard, 1),
            ],
        })
        .expect("resource preconditions should compile");
        let alpha = types.type_var(TypeVarId(0));
        let input = types.resource(alpha);

        let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

        assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
        assert!(!reachability.fail_reachable);
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
        let plan = pattern_dispatch_from_source(SourcePatternRows {
            input_count: 2,
            rows: vec![
                row2(Pattern::Atom("x".to_string()), Pattern::Wildcard, 0),
                row2(Pattern::Wildcard, Pattern::Wildcard, 1),
            ],
        })
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
