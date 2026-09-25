//! Whole incoming rows for the existing return solve. This layer selects
//! source clauses; it neither executes their bodies nor discharges their
//! strict prerequisites.

use std::rc::Rc;

use super::bound_bindings::{FamilyBranches, FrameArena, FrameId, normalize_families};
use super::{ActivationKey, Bindings, HashMap, Term, Ty, Types, project_concrete};
use crate::compiler2::dispatch_reachability::{
    BoundDispatchDomain, BoundDispatchRow, BoundDispatchSource, RefinedRows, dispatch_rows,
};
use crate::compiler2::return_skeleton::{BoundSkeleton, Skeleton, Substitution};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;

type Arena = FrameArena<Term>;

pub(super) struct MemberRows {
    pub(super) clauses: Vec<u32>,
    pub(super) pending: bool,
}

pub(super) struct RowBindings {
    pub(super) dispatch: HashMap<ActivationKey, MemberRows>,
}

pub(super) fn gather_rows(
    bindings: &Bindings,
    plans: &HashMap<ActivationKey, Rc<PatternDispatchPlan<Ty>>>,
    types: &mut Types,
) -> RowBindings {
    let mut arena = Arena::default();
    let mut families = HashMap::new();
    for member in plans.keys().chain(bindings.input_rows.keys()) {
        families
            .entry(member.clone())
            .or_insert_with(|| arena.family(member.clone()));
    }
    let mut raw = HashMap::new();
    for (member, rows) in &bindings.input_rows {
        let family = families[member];
        let mut alternatives = Vec::new();
        for row in rows {
            let evidence = arena.observed_row(member.clone(), row.clone());
            let arguments = row
                .iter()
                .enumerate()
                .map(|(slot, term)| match term {
                    Term::Bottom => BoundSkeleton::new(evidence, Skeleton::Bottom),
                    Term::Shape(source, shape) => {
                        let frame = *families
                            .entry(source.clone())
                            .or_insert_with(|| arena.family(source.clone()));
                        BoundSkeleton::new(frame, shape.clone())
                    }
                    Term::Slot(source, input) => {
                        let frame = *families
                            .entry(source.clone())
                            .or_insert_with(|| arena.family(source.clone()));
                        BoundSkeleton::new(frame, Skeleton::Input(*input))
                    }
                    _ => BoundSkeleton::new(evidence, Skeleton::Input(slot)),
                })
                .collect();
            alternatives.push(Substitution { arguments });
        }
        raw.insert(family, alternatives);
    }
    for (member, family) in &families {
        if member.input_len() == 0 {
            raw.entry(*family)
                .or_insert_with(|| vec![Substitution::in_frame(*family, &[])]);
        }
    }
    let normalized = normalize_families(&mut arena, &raw, &mut |arena, value| {
        normalize_observation(bindings, arena, types, value)
    });
    let mut source = RowSource {
        bindings,
        arena: &mut arena,
        normalized: &normalized,
    };
    let mut domain = BoundDispatchDomain {
        types,
        source: &mut source,
    };
    let mut dispatch = HashMap::new();
    for (member, plan) in plans {
        let family = families[member];
        let inputs = normalized
            .rows
            .get(&family)
            .into_iter()
            .flatten()
            .cloned()
            .map(|row| BoundDispatchRow::new(plan, row));
        let reached = dispatch_rows(&mut domain, plan, inputs);
        let mut clauses = reached
            .outcomes
            .into_iter()
            .map(|(outcome, _)| {
                plan.outcome(outcome)
                    .expect("dispatch outcome belongs to its plan")
                    .body_id
            })
            .collect::<Vec<_>>();
        clauses.sort_unstable();
        clauses.dedup();
        dispatch.insert(
            member.clone(),
            MemberRows {
                clauses,
                pending: reached.pending
                    || !normalized.rows.contains_key(&family)
                    || normalized.pending.contains(&family),
            },
        );
    }
    RowBindings { dispatch }
}

struct RowSource<'a> {
    bindings: &'a Bindings,
    arena: &'a mut Arena,
    normalized: &'a FamilyBranches,
}

impl BoundDispatchSource for RowSource<'_> {
    type Frame = FrameId;

    fn input_rows(&mut self, frame: &FrameId) -> RefinedRows<Substitution<FrameId>> {
        if let Some(inputs) = self.arena.inputs(*frame) {
            return RefinedRows {
                rows: vec![inputs.clone()],
                pending: false,
            };
        }
        if self.arena.observations(*frame).is_some() {
            return RefinedRows {
                rows: vec![self.arena.identity(*frame)],
                pending: false,
            };
        }
        RefinedRows {
            rows: self.normalized.rows.get(frame).cloned().unwrap_or_default(),
            pending: !self.normalized.rows.contains_key(frame) || self.normalized.pending.contains(frame),
        }
    }

    fn observed(&mut self, value: &BoundSkeleton<FrameId>, types: &mut Types) -> Option<Ty> {
        observed(self.bindings, self.arena, value, types)
    }

    fn struct_name(&self, module: super::ModuleId) -> Option<super::ModuleName> {
        self.bindings.module_names.get(&module).cloned()
    }

    fn rebind(&mut self, frame: &FrameId, inputs: &Substitution<FrameId>) -> FrameId {
        self.arena.rebind(*frame, inputs)
    }
}

fn observed(bindings: &Bindings, arena: &Arena, value: &BoundSkeleton<FrameId>, types: &mut Types) -> Option<Ty> {
    match &value.shape {
        Skeleton::Input(slot) => arena.observation(value.frame, *slot).and_then(|term| match term {
            Term::Settled(ty) => Some(*ty),
            Term::Evidence(input) => Some(input.ty()),
            Term::Return(source) => bindings.externals.get(source).copied(),
            _ => None,
        }),
        // These observations belong to the unchanged activation environment.
        // An applied frame must obtain its own evidence, not borrow the old
        // aggregate answer to an operation with different operands.
        Skeleton::Ground(value_id) => arena
            .family_source(value.frame)
            .and_then(|source| bindings.value_types.get(source))
            .and_then(|values| values.get(value_id))
            .copied(),
        Skeleton::Result { callsite, .. } => {
            let source = arena.family_source(value.frame)?;
            let results = bindings.results.get(&(source.clone(), *callsite))?;
            let [result] = results.as_slice() else { return None };
            match result {
                Term::Settled(ty) => Some(*ty),
                Term::Evidence(input) => Some(input.ty()),
                Term::Return(source) => bindings.externals.get(source).copied(),
                _ => None,
            }
        }
        Skeleton::Project { of, step } => {
            let subject = BoundSkeleton::new(value.frame, (**of).clone());
            let ty = observed(bindings, arena, &subject, types)?;
            match project_concrete(ty, step, types) {
                Term::Bottom => Some(types.none()),
                Term::Settled(ty) => Some(ty),
                _ => unreachable!("concrete projection returns a type or an impossible branch"),
            }
        }
        _ => None,
    }
}

fn normalize_observation(
    bindings: &Bindings,
    arena: &mut Arena,
    types: &mut Types,
    value: BoundSkeleton<FrameId>,
) -> Option<BoundSkeleton<FrameId>> {
    if matches!(value.shape, Skeleton::Bottom) {
        return Some(value);
    }
    if let Skeleton::Project { of, step } = &value.shape {
        let subject = normalize_observation(bindings, arena, types, BoundSkeleton::new(value.frame, (**of).clone()))?;
        if matches!(subject.shape, Skeleton::Bottom) {
            return Some(subject);
        }
        let ty = observed(bindings, arena, &subject, types)?;
        return match project_concrete(ty, step, types) {
            Term::Bottom => Some(BoundSkeleton::new(value.frame, Skeleton::Bottom)),
            Term::Settled(projected) if types.is_empty(&projected) => {
                Some(BoundSkeleton::new(value.frame, Skeleton::Bottom))
            }
            Term::Settled(projected) => {
                let frame = arena.derived_observation(subject, Term::Settled(projected));
                Some(BoundSkeleton::new(frame, Skeleton::Input(0)))
            }
            _ => unreachable!("concrete projection returns a type or an impossible branch"),
        };
    }
    let ty = observed(bindings, arena, &value, types)?;
    Some(if types.is_empty(&ty) {
        BoundSkeleton::new(value.frame, Skeleton::Bottom)
    } else {
        value
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Pattern, Spanned};
    use crate::compiler2::identity::{FunctionId, RootId};
    use crate::compiler2::semantic::ProjectStep;
    use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};

    #[test]
    fn projections_of_one_observed_tuple_union_keep_their_joint_alternative() {
        let mut types = Types::new();
        let source = activation(&mut types, 0, 1);
        let callee = activation(&mut types, 1, 2);
        let left = types.atom_lit("left");
        let right = types.atom_lit("right");
        let first = types.tuple(&[left, right]);
        let second = types.tuple(&[right, left]);
        let paired = types.union(first, second);
        let mut bindings = Bindings::default();
        bindings.insert_input_row(source.clone(), vec![Term::Settled(paired)]);
        bindings.insert_input_row(
            callee.clone(),
            (0..2)
                .map(|slot| {
                    Term::Shape(
                        source.clone(),
                        Skeleton::project(Skeleton::Input(0), ProjectStep::TupleField(slot)),
                    )
                })
                .collect(),
        );
        let plans = HashMap::from([(
            callee.clone(),
            plan(vec![
                vec![Pattern::Atom("left".into()), Pattern::Atom("left".into())],
                vec![Pattern::Wildcard, Pattern::Wildcard],
            ]),
        )]);
        let rows = gather_rows(&bindings, &plans, &mut types);
        let selected = &rows.dispatch[&callee];
        assert!(!selected.pending);
        assert_eq!(
            selected.clauses,
            vec![1],
            "projecting {{left,right}} | {{right,left}} must not manufacture the crossed argument row (left,left)"
        );
    }

    #[test]
    fn a_union_argument_is_known_alternatives_not_an_unobserved_input() {
        let mut types = Types::new();
        let source = activation(&mut types, 0, 2);
        let callee = activation(&mut types, 1, 1);
        let mut bindings = Bindings::default();
        bindings.insert_input_row(
            source.clone(),
            vec![
                Term::Settled(types.atom_lit("left")),
                Term::Settled(types.atom_lit("right")),
            ],
        );
        bindings.insert_input_row(
            callee.clone(),
            vec![Term::Shape(
                source,
                Skeleton::union(Skeleton::Input(0), Skeleton::Input(1)),
            )],
        );
        let plans = HashMap::from([(
            callee.clone(),
            plan(vec![
                vec![Pattern::Atom("left".into())],
                vec![Pattern::Atom("right".into())],
            ]),
        )]);
        let rows = gather_rows(&bindings, &plans, &mut types);
        assert!(
            !rows.dispatch[&callee].pending,
            "a source union is not missing evidence"
        );
        assert_eq!(rows.dispatch[&callee].clauses, vec![0, 1]);
    }

    fn activation(types: &mut Types, function: u32, arity: usize) -> ActivationKey {
        ActivationKey::from_inputs(
            RootId::for_test(0),
            FunctionId::from_coordinate(function),
            &vec![types.any(); arity],
            types,
        )
    }

    fn plan(patterns: Vec<Vec<Pattern>>) -> Rc<PatternDispatchPlan<Ty>> {
        let arity = patterns[0].len();
        Rc::new(
            pattern_dispatch_from_source(SourcePatternRows::lexical(
                arity,
                patterns
                    .into_iter()
                    .enumerate()
                    .map(|(body_id, patterns)| PatternRow {
                        patterns: patterns.into_iter().map(Spanned::dummy).collect(),
                        preconditions: Vec::new(),
                        guard: None,
                        body_id: body_id as u32,
                    })
                    .collect(),
            ))
            .unwrap(),
        )
    }

    #[test]
    fn incoming_whole_row_fixpoint_selects_aligned_clauses_without_crossing_columns() {
        let mut types = Types::new();
        let grow = activation(&mut types, 0, 2);
        let aligned = activation(&mut types, 1, 2);
        let mut bindings = Bindings::default();
        bindings.insert_input_row(
            grow.clone(),
            vec![
                Term::Settled(types.atom_lit("left")),
                Term::Settled(types.atom_lit("right")),
            ],
        );
        bindings.insert_input_row(
            grow.clone(),
            (0..2)
                .map(|slot| Term::Shape(grow.clone(), Skeleton::Tuple(vec![Skeleton::Input(slot)])))
                .collect(),
        );
        bindings.insert_input_row(
            aligned.clone(),
            (0..2).map(|slot| Term::Slot(grow.clone(), slot)).collect(),
        );
        bindings.insert_input_row(
            aligned.clone(),
            (0..2)
                .map(|slot| {
                    Term::Shape(
                        aligned.clone(),
                        Skeleton::project(Skeleton::Input(slot), ProjectStep::TupleField(0)),
                    )
                })
                .collect(),
        );
        let plans = HashMap::from([(
            aligned.clone(),
            plan(vec![
                vec![Pattern::Atom("left".into()), Pattern::Atom("right".into())],
                vec![
                    Pattern::Tuple(vec![Spanned::dummy(Pattern::Wildcard)]),
                    Pattern::Tuple(vec![Spanned::dummy(Pattern::Wildcard)]),
                ],
                vec![Pattern::Wildcard, Pattern::Wildcard],
            ]),
        )]);
        let result = gather_rows(&bindings, &plans, &mut types);
        let selected = &result.dispatch[&aligned];
        assert!(!selected.pending);
        let mut clauses = selected.clauses.clone();
        clauses.sort_unstable();
        clauses.dedup();
        assert_eq!(clauses, vec![0, 1]);
    }

    #[test]
    fn repeated_concrete_tail_observations_share_one_original_source_port() {
        let mut types = Types::new();
        let member = activation(&mut types, 0, 1);
        let integer = types.int();
        let list = types.list(integer);
        let mut bindings = Bindings::default();
        bindings.insert_input_row(member.clone(), vec![Term::Settled(list)]);
        bindings.insert_input_row(
            member.clone(),
            vec![Term::Shape(
                member.clone(),
                Skeleton::project(Skeleton::Input(0), ProjectStep::ListTail),
            )],
        );
        let plans = HashMap::from([(member.clone(), plan(vec![vec![Pattern::Wildcard]]))]);
        let result = gather_rows(&bindings, &plans, &mut types);
        assert!(!result.dispatch[&member].pending);
        assert_eq!(result.dispatch[&member].clauses, vec![0]);
    }

    #[test]
    fn rebound_operations_do_not_borrow_the_original_aggregate_observation() {
        use crate::compiler2::body::ValueId;
        let mut types = Types::new();
        let member = activation(&mut types, 0, 1);
        let value = ValueId::from_u32(1);
        let integer = types.int();
        let mut bindings = Bindings::default();
        bindings
            .value_types
            .insert(member.clone(), HashMap::from([(value, integer)]));
        let mut arena = Arena::default();
        let family = arena.family(member.clone());
        let source = BoundSkeleton::new(family, Skeleton::Ground(value));
        assert_eq!(observed(&bindings, &arena, &source, &mut types), Some(integer));
        let evidence = arena.observed_row(member, vec![Term::Settled(types.float())]);
        let applied = arena.rebind(family, &arena.identity(evidence));
        let changed = BoundSkeleton::new(applied, Skeleton::Ground(value));
        assert_eq!(observed(&bindings, &arena, &changed, &mut types), None);
    }

    #[test]
    fn wildcard_dispatch_preserves_missing_empty_and_zero_arity_families() {
        let mut types = Types::new();
        let missing = activation(&mut types, 0, 1);
        let empty = activation(&mut types, 1, 1);
        let zero = activation(&mut types, 2, 0);
        let dead = activation(&mut types, 3, 1);
        let mut bindings = Bindings::default();
        bindings.input_rows.insert(empty.clone(), Vec::new());
        bindings.insert_input_row(dead.clone(), vec![Term::Settled(types.none())]);
        let plans = HashMap::from([
            (missing.clone(), plan(vec![vec![Pattern::Wildcard]])),
            (empty.clone(), plan(vec![vec![Pattern::Wildcard]])),
            (dead.clone(), plan(vec![vec![Pattern::Wildcard]])),
            (zero.clone(), plan(vec![vec![]])),
        ]);
        let result = gather_rows(&bindings, &plans, &mut types);
        assert!(result.dispatch[&missing].pending);
        assert!(result.dispatch[&missing].clauses.is_empty());
        for member in [&empty, &dead] {
            assert!(!result.dispatch[member].pending);
            assert!(result.dispatch[member].clauses.is_empty());
        }
        assert!(!result.dispatch[&zero].pending);
        assert_eq!(result.dispatch[&zero].clauses.len(), 1);
    }
}
