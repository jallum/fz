//! Source-qualified frames for the existing return equation system.
//!
//! A row-branch fixpoint preserves complete source transfers and their shared
//! producer references. The existing scalar equation kernel still owns value
//! types, escape, and completion. Applied frames name a source vocabulary and
//! an ordered substitution; dispatch owns residual proof restrictions. Derived
//! observations canonicalize settled type evidence for proofs, not runtime
//! producers. No key contains a predecessor environment.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::compiler2::identity::ActivationKey;
use crate::compiler2::return_skeleton::{BoundSkeleton, Skeleton, Substitution};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct FrameId(usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Frame<Observation> {
    Family(ActivationKey),
    Observed {
        source: ActivationKey,
        row: Vec<Observation>,
    },
    Applied {
        source: ActivationKey,
        inputs: Substitution<FrameId>,
    },
    /// A derived type observation for proof evaluation. The original source
    /// port distinguishes producers even when their observed types agree.
    DerivedObservation {
        origin: BoundSkeleton<FrameId>,
        observation: Observation,
    },
}

/// A solve-local immutable frame graph. Observations retain their existing
/// owner's representation. Proof restrictions remain in dispatch rows;
/// plan-local subject IDs are not portable bindings for another function.
#[derive(Debug)]
pub(super) struct FrameArena<Observation> {
    frames: Vec<Frame<Observation>>,
    index: HashMap<Frame<Observation>, FrameId>,
}

impl<Observation> Default for FrameArena<Observation> {
    fn default() -> Self {
        Self {
            frames: Vec::new(),
            index: HashMap::new(),
        }
    }
}

impl<Observation: Clone + Eq + Hash> FrameArena<Observation> {
    pub(super) fn family(&mut self, source: ActivationKey) -> FrameId {
        self.intern(Frame::Family(source))
    }

    /// Observed slots use `Input(slot)` in this frame. They are evidence
    /// coordinates, never synthetic source `Ground(ValueId)` addresses.
    pub(super) fn observed_row(&mut self, source: ActivationKey, row: Vec<Observation>) -> FrameId {
        assert_eq!(
            row.len(),
            source.input_len(),
            "observed evidence is a complete ordered row"
        );
        self.intern(Frame::Observed { source, row })
    }

    /// Resolving input aliases only follows fixed applied frames; it never
    /// chooses an alternative of an open recursive family.
    pub(super) fn applied(&mut self, source: ActivationKey, inputs: Substitution<FrameId>) -> FrameId {
        assert_eq!(
            inputs.arguments.len(),
            source.input_len(),
            "an application binds every semantic input"
        );
        let inputs = self.normalize(&inputs);
        self.intern(Frame::Applied { source, inputs })
    }

    pub(super) fn normalize(&self, inputs: &Substitution<FrameId>) -> Substitution<FrameId> {
        inputs.compose(&mut |frame, slot| self.input(*frame, slot))
    }

    /// Rebinding replaces the entire ordered environment in the same source
    /// vocabulary. It extracts the original source from an applied
    /// frame, so rebinding an already rebound frame creates no parent chain.
    pub(super) fn rebind(&mut self, frame: FrameId, inputs: &Substitution<FrameId>) -> FrameId {
        assert!(
            self.derived_origin(frame).is_none(),
            "proof observations are not function input environments"
        );
        let source = self.source(frame).clone();
        self.applied(source, inputs.clone())
    }

    pub(super) fn identity(&self, frame: FrameId) -> Substitution<FrameId> {
        Substitution {
            arguments: (0..match &self.frames[frame.0] {
                Frame::DerivedObservation { .. } => 1,
                _ => self.source(frame).input_len(),
            })
                .map(|slot| BoundSkeleton::new(frame, Skeleton::Input(slot)))
                .collect(),
        }
    }

    pub(super) fn source(&self, frame: FrameId) -> &ActivationKey {
        match &self.frames[frame.0] {
            Frame::Family(source) | Frame::Observed { source, .. } | Frame::Applied { source, .. } => source,
            Frame::DerivedObservation { origin, .. } => self.source(origin.frame),
        }
    }

    pub(super) fn family_source(&self, frame: FrameId) -> Option<&ActivationKey> {
        match &self.frames[frame.0] {
            Frame::Family(source) => Some(source),
            Frame::Observed { .. } | Frame::Applied { .. } | Frame::DerivedObservation { .. } => None,
        }
    }

    pub(super) fn inputs(&self, frame: FrameId) -> Option<&Substitution<FrameId>> {
        match &self.frames[frame.0] {
            Frame::Applied { inputs, .. } => Some(inputs),
            Frame::Family(_) | Frame::Observed { .. } | Frame::DerivedObservation { .. } => None,
        }
    }

    pub(super) fn input(&self, frame: FrameId, slot: usize) -> Option<BoundSkeleton<FrameId>> {
        self.inputs(frame)
            .and_then(|inputs| inputs.arguments.get(slot))
            .cloned()
    }

    pub(super) fn observations(&self, frame: FrameId) -> Option<&[Observation]> {
        match &self.frames[frame.0] {
            Frame::Observed { row, .. } => Some(row),
            Frame::DerivedObservation { observation, .. } => Some(std::slice::from_ref(observation)),
            Frame::Family(_) | Frame::Applied { .. } => None,
        }
    }

    pub(super) fn observation(&self, frame: FrameId, slot: usize) -> Option<&Observation> {
        self.observations(frame).and_then(|row| row.get(slot))
    }

    pub(super) fn derived_origin(&self, frame: FrameId) -> Option<&BoundSkeleton<FrameId>> {
        match &self.frames[frame.0] {
            Frame::DerivedObservation { origin, .. } => Some(origin),
            Frame::Family(_) | Frame::Observed { .. } | Frame::Applied { .. } => None,
        }
    }

    /// Canonicalize a settled observation used to decide type proofs. Its
    /// coordinate is `Input(0)` even when the source function has another
    /// arity. The actual source operation and its completion remain elsewhere.
    ///
    /// Repeated derivation unwraps the existing origin, not its predecessor
    /// frame. Projection paths are represented by the resulting observation
    /// for this purpose; the original input slot/Ground/Result port remains
    /// part of the key, so equal types do not merge distinct source values.
    pub(super) fn derived_observation(
        &mut self,
        mut origin: BoundSkeleton<FrameId>,
        observation: Observation,
    ) -> FrameId {
        loop {
            origin = origin.resolve(&mut |frame, slot| self.input(*frame, slot));
            if let Skeleton::Project { of, .. } = origin.shape {
                origin.shape = *of;
                continue;
            }
            if let Some(original) = self.derived_origin(origin.frame) {
                assert_eq!(
                    origin.shape,
                    Skeleton::Input(0),
                    "a derived proof frame has only its observed coordinate"
                );
                origin = original.clone();
                continue;
            }
            break;
        }
        self.intern(Frame::DerivedObservation { origin, observation })
    }

    fn intern(&mut self, frame: Frame<Observation>) -> FrameId {
        if let Some(id) = self.index.get(&frame) {
            return *id;
        }
        let id = FrameId(self.frames.len());
        self.frames.push(frame.clone());
        self.index.insert(frame, id);
        id
    }
}

/// Whole-row counterparts of the existing equation kernel's branch sets.
/// Pending records missing normalization inputs, not execution completion;
/// constructor children and strict body prerequisites still belong to that
/// kernel. A known empty alias cycle has no branches and is not pending.
#[derive(Debug, Default)]
pub(super) struct FamilyBranches {
    pub(super) rows: HashMap<FrameId, Vec<Substitution<FrameId>>>,
    pub(super) pending: HashSet<FrameId>,
    pub(super) dependencies: HashMap<FrameId, HashSet<FrameId>>,
}

/// Compute branch sets from fixed source transfers and the standing sets,
/// starting with no branches. Never substitute an unresolved raw recursive
/// transfer into itself: `A = P | Unwrap(A)` reads A's already reached heads.
/// Each expansion replaces a complete row together. A constructor in any
/// output guards the entire row: its children AND its sibling columns remain
/// symbolic references. Requiring a head in every column would enumerate
/// `P = Seed | ({P.0}, P.1)` forever merely to expose its unchanged second
/// input. Only unguarded aliases/projections read standing alternatives.
///
/// The existing value owner normalizes terminal leaves and concrete
/// projections. `None` means unresolved, while `Bottom` in any strict input
/// eliminates that whole row. No widening or iteration budget is introduced;
/// termination follows only for products whose normalized branch sets are
/// finite, such as synchronized wrapping and its cancelling projections.
pub(super) fn normalize_families<Observation: Clone + Eq + Hash>(
    arena: &mut FrameArena<Observation>,
    raw: &HashMap<FrameId, Vec<Substitution<FrameId>>>,
    normalize_value: &mut impl FnMut(&mut FrameArena<Observation>, BoundSkeleton<FrameId>) -> Option<BoundSkeleton<FrameId>>,
) -> FamilyBranches {
    let mut result = FamilyBranches {
        rows: raw.keys().map(|frame| (*frame, Vec::new())).collect(),
        ..FamilyBranches::default()
    };
    let mut families: Vec<_> = raw.keys().copied().collect();
    families.sort_unstable();
    loop {
        let mut moved = false;
        for family in &families {
            let expanded = expand_rows(arena, &raw[family], &result.rows, normalize_value);
            let standing = result.rows.get_mut(family).expect("each raw family has a branch set");
            for row in expanded.rows {
                if !standing.contains(&row) {
                    standing.push(row);
                    moved = true;
                }
            }
            result
                .dependencies
                .entry(*family)
                .or_default()
                .extend(expanded.dependencies);
            if expanded.pending {
                result.pending.insert(*family);
            }
        }
        if !moved {
            break;
        }
    }
    loop {
        let mut moved = false;
        for family in &families {
            if result.dependencies[family]
                .iter()
                .any(|dependency| result.pending.contains(dependency))
            {
                moved |= result.pending.insert(*family);
            }
        }
        if !moved {
            break;
        }
    }
    result
}

#[derive(Default)]
struct RowExpansion {
    rows: Vec<Substitution<FrameId>>,
    dependencies: HashSet<FrameId>,
    pending: bool,
}

fn expand_rows<Observation: Clone + Eq + Hash>(
    arena: &mut FrameArena<Observation>,
    raw: &[Substitution<FrameId>],
    standing: &HashMap<FrameId, Vec<Substitution<FrameId>>>,
    normalize_value: &mut impl FnMut(&mut FrameArena<Observation>, BoundSkeleton<FrameId>) -> Option<BoundSkeleton<FrameId>>,
) -> RowExpansion {
    let mut result = RowExpansion::default();
    let mut work: Vec<_> = raw.iter().rev().cloned().collect();
    let mut seen = HashSet::new();
    while let Some(row) = work.pop() {
        let mut row = arena.normalize(&row);
        if !seen.insert(row.clone()) {
            continue;
        }
        let mut pending = false;
        for value in &mut row.arguments {
            if open_family(arena, value).is_some() || is_constructor(&value.shape) || value.shape == Skeleton::Bottom {
                continue;
            }
            match normalize_value(arena, value.clone()) {
                Some(normalized) => *value = normalized,
                None => pending = true,
            }
        }
        if row.arguments.iter().any(|value| value.shape == Skeleton::Bottom) {
            continue;
        }
        let mut dependencies = HashSet::new();
        for value in &row.arguments {
            family_dependencies(arena, value, &mut dependencies);
        }
        pending |= dependencies.iter().any(|frame| !standing.contains_key(frame));
        result.dependencies.extend(dependencies);
        let guarded = row.arguments.iter().any(|value| is_constructor(&value.shape));
        result.pending |= pending;
        if guarded {
            if !result.rows.contains(&row) {
                result.rows.push(row);
            }
            continue;
        }
        if pending {
            continue;
        }
        let family = row.arguments.iter().find_map(|value| open_family(arena, value));
        if let Some(family) = family {
            for replacement in standing[&family].iter().rev() {
                work.push(row.apply_once(&family, replacement, &mut |frame, inputs| arena.rebind(*frame, inputs)));
            }
        } else if !result.rows.contains(&row) {
            result.rows.push(row);
        }
    }
    result
}

fn is_constructor(shape: &Skeleton) -> bool {
    matches!(
        shape,
        Skeleton::Tuple(_) | Skeleton::List { .. } | Skeleton::Map(_) | Skeleton::Struct(_, _)
    )
}

fn open_family<Observation: Clone + Eq + Hash>(
    arena: &FrameArena<Observation>,
    value: &BoundSkeleton<FrameId>,
) -> Option<FrameId> {
    match &value.shape {
        Skeleton::Input(_) if arena.family_source(value.frame).is_some() => Some(value.frame),
        Skeleton::Project { of, .. } => open_family(arena, &BoundSkeleton::new(value.frame, (**of).clone())),
        _ => None,
    }
}

fn family_dependencies<Observation: Clone + Eq + Hash>(
    arena: &FrameArena<Observation>,
    value: &BoundSkeleton<FrameId>,
    out: &mut HashSet<FrameId>,
) {
    let value = value.resolve(&mut |frame, slot| arena.input(*frame, slot));
    let mut child = |shape: &Skeleton| family_dependencies(arena, &BoundSkeleton::new(value.frame, shape.clone()), out);
    match &value.shape {
        Skeleton::Input(_) if arena.family_source(value.frame).is_some() => {
            out.insert(value.frame);
        }
        Skeleton::Union(shapes) | Skeleton::Tuple(shapes) => shapes.iter().for_each(&mut child),
        Skeleton::List { element, .. } => child(element),
        Skeleton::Map(fields) | Skeleton::Struct(_, fields) => fields.iter().for_each(|(_, shape)| child(shape)),
        Skeleton::Project { of, .. } => child(of),
        Skeleton::Bottom | Skeleton::Ground(_) | Skeleton::Input(_) | Skeleton::Result { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::body::ValueId;
    use crate::compiler2::identity::{FunctionId, RootId};
    use crate::compiler2::semantic::ProjectStep;
    use crate::compiler2::types::{Ty, Types};

    fn observed_projection(
        arena: &mut FrameArena<Ty>,
        types: &mut Types,
        value: BoundSkeleton<FrameId>,
    ) -> Option<BoundSkeleton<FrameId>> {
        match &value.shape {
            Skeleton::Input(slot) if arena.observation(value.frame, *slot).is_some() => Some(value),
            Skeleton::Project { of, step } => {
                let Skeleton::Input(slot) = **of else { return None };
                let ty = *arena.observation(value.frame, slot)?;
                match super::super::project_concrete(ty, step, types) {
                    super::super::Term::Bottom => Some(BoundSkeleton::new(value.frame, Skeleton::Bottom)),
                    super::super::Term::Settled(projected) => {
                        let frame = arena
                            .derived_observation(BoundSkeleton::new(value.frame, Skeleton::Input(slot)), projected);
                        Some(BoundSkeleton::new(frame, Skeleton::Input(0)))
                    }
                    _ => unreachable!("the existing concrete projector returns a type or bottom"),
                }
            }
            _ => None,
        }
    }

    #[test]
    fn family_branch_fixpoint_cancels_joint_unwrap_without_building_projection_histories() {
        let mut types = Types::new();
        let grow = activation(&mut types, 0, 2);
        let aligned = activation(&mut types, 1, 2);
        let mut arena = FrameArena::<Ty>::default();
        let p = arena.family(grow.clone());
        let a = arena.family(aligned);
        let evidence = arena.observed_row(grow, vec![types.atom_lit("left"), types.atom_lit("right")]);
        let seed = arena.identity(evidence);
        let wrapped = Substitution::in_frame(
            p,
            &[
                Skeleton::Tuple(vec![Skeleton::Input(0)]),
                Skeleton::Tuple(vec![Skeleton::Input(1)]),
            ],
        );
        let unwrap = Substitution::in_frame(
            a,
            &[
                Skeleton::project(Skeleton::Input(0), ProjectStep::TupleField(0)),
                Skeleton::project(Skeleton::Input(1), ProjectStep::TupleField(0)),
            ],
        );
        let raw = HashMap::from([
            (p, vec![seed.clone(), wrapped.clone()]),
            (a, vec![arena.identity(p), unwrap]),
        ]);
        let branches = normalize_families(&mut arena, &raw, &mut |arena, value| {
            observed_projection(arena, &mut types, value)
        });
        for family in [p, a] {
            assert_eq!(branches.rows[&family].len(), 2);
            assert!(branches.rows[&family].contains(&seed));
            assert!(branches.rows[&family].contains(&wrapped));
        }
        assert!(branches.pending.is_empty());
        assert!(branches.dependencies[&a].contains(&p));
        assert!(branches.dependencies[&a].contains(&a));
    }

    #[test]
    fn family_branch_fixpoint_keeps_one_sided_growth_symbolic() {
        let mut types = Types::new();
        let source = activation(&mut types, 0, 2);
        let mut arena = FrameArena::<Ty>::default();
        let p = arena.family(source.clone());
        let evidence = arena.observed_row(source, vec![types.atom_lit("left"), types.atom_lit("right")]);
        let seed = arena.identity(evidence);
        let first_seed = seed.arguments[0].clone();
        let growing = Substitution::in_frame(p, &[Skeleton::Tuple(vec![Skeleton::Input(0)]), Skeleton::Input(1)]);
        let raw = HashMap::from([(p, vec![seed, growing])]);
        let mut passes = 0;
        let mut callbacks = 0;
        let branches = normalize_families(&mut arena, &raw, &mut |arena, value| {
            callbacks += 1;
            if value == first_seed {
                passes += 1;
                assert!(
                    passes <= 64,
                    "one unchanged column unfolded its partner's constructor history for {passes} passes ({callbacks} callbacks)"
                );
            }
            observed_projection(arena, &mut types, value)
        });
        assert!(!branches.pending.contains(&p));
        assert!(
            branches.rows[&p].len() <= 2,
            "the recursive row stays a transfer, not concrete depth alternatives"
        );
    }

    #[test]
    fn a_constructor_guard_keeps_its_missing_sibling_pending_without_erasing_the_row() {
        let mut types = Types::new();
        let source = activation(&mut types, 0, 2);
        let absent_source = activation(&mut types, 1, 2);
        let mut arena = FrameArena::<Ty>::default();
        let p = arena.family(source);
        let absent = arena.family(absent_source);
        let guarded = Substitution {
            arguments: vec![
                BoundSkeleton::new(p, Skeleton::Tuple(vec![Skeleton::Input(0)])),
                BoundSkeleton::new(absent, Skeleton::Input(1)),
            ],
        };
        let raw = HashMap::from([(p, vec![guarded.clone()])]);
        let branches = normalize_families(&mut arena, &raw, &mut |arena, value| {
            observed_projection(arena, &mut types, value)
        });
        assert_eq!(branches.rows[&p], vec![guarded]);
        assert!(branches.pending.contains(&p));
        assert!(branches.dependencies[&p].contains(&absent));
        assert!(branches.dependencies[&p].contains(&p));
    }

    #[test]
    fn repeated_list_tail_proof_observations_keep_a_canonical_source_origin() {
        let mut types = Types::new();
        let source = activation(&mut types, 0, 1);
        let mut arena = FrameArena::<Ty>::default();
        let p = arena.family(source.clone());
        let int = types.int();
        let list = types.list(int);
        let evidence = arena.observed_row(source, vec![list]);
        let seed = arena.identity(evidence);
        let first_seed = seed.arguments[0].clone();
        let tail = Substitution::in_frame(p, &[Skeleton::project(Skeleton::Input(0), ProjectStep::ListTail)]);
        let raw = HashMap::from([(p, vec![seed, tail])]);
        let mut passes = 0;
        let branches = normalize_families(&mut arena, &raw, &mut |arena, value| {
            if value == first_seed {
                passes += 1;
                assert!(
                    passes <= 64,
                    "stable list-tail proof type accumulated projection syntax for {passes} passes"
                );
            }
            observed_projection(arena, &mut types, value)
        });
        assert!(!branches.pending.contains(&p));
        assert!(branches.rows[&p].len() <= 2);
    }

    #[test]
    fn family_branch_fixpoint_keeps_a_mismatched_seed_whole_and_drops_its_impossible_unwrap() {
        let mut types = Types::new();
        let grow = activation(&mut types, 0, 2);
        let aligned = activation(&mut types, 1, 2);
        let mut arena = FrameArena::<Ty>::default();
        let p = arena.family(grow.clone());
        let a = arena.family(aligned);
        let evidence = arena.observed_row(grow, vec![types.atom_lit("left"), types.atom_lit("right")]);
        let seed = arena.identity(evidence);
        let mismatched = Substitution::in_frame(
            evidence,
            &[Skeleton::Tuple(vec![Skeleton::Input(0)]), Skeleton::Input(1)],
        );
        let wrapped = Substitution::in_frame(
            p,
            &[
                Skeleton::Tuple(vec![Skeleton::Input(0)]),
                Skeleton::Tuple(vec![Skeleton::Input(1)]),
            ],
        );
        let unwrap = Substitution::in_frame(
            a,
            &[
                Skeleton::project(Skeleton::Input(0), ProjectStep::TupleField(0)),
                Skeleton::project(Skeleton::Input(1), ProjectStep::TupleField(0)),
            ],
        );
        let raw = HashMap::from([
            (p, vec![seed.clone(), wrapped.clone(), mismatched.clone()]),
            (a, vec![arena.identity(p), unwrap]),
        ]);
        let branches = normalize_families(&mut arena, &raw, &mut |arena, value| {
            observed_projection(arena, &mut types, value)
        });
        assert_eq!(branches.rows[&a].len(), 3);
        for expected in [seed, wrapped, mismatched] {
            assert!(branches.rows[&a].contains(&expected));
        }
        assert!(branches.pending.is_empty());
    }

    #[test]
    fn family_branch_fixpoint_distinguishes_missing_producers_from_closed_alias_cycles() {
        let mut types = Types::new();
        let mut arena = FrameArena::<Ty>::default();
        let a = arena.family(activation(&mut types, 0, 1));
        let missing = arena.family(activation(&mut types, 1, 1));
        let cycle = arena.family(activation(&mut types, 2, 1));
        let evidence = arena.observed_row(arena.source(a).clone(), vec![types.int()]);
        let seed = arena.identity(evidence);
        let raw = HashMap::from([
            (a, vec![seed.clone(), arena.identity(missing)]),
            (cycle, vec![arena.identity(cycle)]),
        ]);
        let branches = normalize_families(&mut arena, &raw, &mut |arena, value| {
            observed_projection(arena, &mut types, value)
        });
        assert_eq!(branches.rows[&a], vec![seed]);
        assert!(branches.pending.contains(&a));
        assert!(branches.rows[&cycle].is_empty());
        assert!(!branches.pending.contains(&cycle));
    }

    fn activation(types: &mut Types, function: u32, arity: usize) -> ActivationKey {
        let inputs = vec![types.any(); arity];
        ActivationKey::from_inputs(
            RootId::for_test(0),
            FunctionId::from_coordinate(function),
            &inputs,
            types,
        )
    }

    #[test]
    fn mixed_constructor_keeps_local_operation_and_supplied_evidence_in_their_own_frames() {
        let mut types = Types::new();
        let source = activation(&mut types, 0, 2);
        let producer = activation(&mut types, 1, 2);
        let mut arena = FrameArena::<u32>::default();
        let family = arena.family(source.clone());
        let evidence = arena.observed_row(producer.clone(), vec![7, 9]);
        let replacement = arena.identity(evidence);
        let original = BoundSkeleton::new(
            family,
            Skeleton::Tuple(vec![Skeleton::Input(0), Skeleton::Ground(ValueId::from_u32(7))]),
        );
        let rebound = original.apply_once(&family, &replacement, &mut |frame, row| arena.rebind(*frame, row));
        let supplied = rebound.project(ProjectStep::TupleField(0), &mut |frame, slot| arena.input(*frame, slot));
        let local = rebound.project(ProjectStep::TupleField(1), &mut |frame, slot| arena.input(*frame, slot));
        assert_eq!(supplied, replacement.arguments[0]);
        assert_eq!(arena.observation(supplied.frame, 0), Some(&7));
        assert_eq!(arena.source(supplied.frame), &producer);
        assert_eq!(arena.source(local.frame), &source);
        assert_eq!(local.shape, Skeleton::Ground(ValueId::from_u32(7)));
        assert_eq!(arena.rebind(rebound.frame, &replacement), rebound.frame);
        assert!(
            arena.input(family, 0).is_none(),
            "a family root stays an open equation reference"
        );
    }

    #[test]
    fn aligned_projection_after_synchronized_wrap_returns_to_the_same_applied_frame() {
        let mut types = Types::new();
        let grow = activation(&mut types, 0, 2);
        let aligned = activation(&mut types, 1, 2);
        let mut arena = FrameArena::<u32>::default();
        let family = arena.family(grow);
        let identity = arena.identity(family);
        let application = arena.applied(aligned.clone(), identity.clone());
        let wrap = Substitution::in_frame(
            family,
            &[
                Skeleton::Tuple(vec![Skeleton::Input(0)]),
                Skeleton::Tuple(vec![Skeleton::Input(1)]),
            ],
        );
        let wrapped_application = arena.rebind(application, &wrap);
        let recursive_arguments = Substitution::in_frame(
            wrapped_application,
            &[
                Skeleton::project(Skeleton::Input(0), ProjectStep::TupleField(0)),
                Skeleton::project(Skeleton::Input(1), ProjectStep::TupleField(0)),
            ],
        );
        let normalized = recursive_arguments.compose(&mut |frame, slot| arena.input(*frame, slot));
        assert_eq!(normalized, identity);
        assert_eq!(arena.applied(aligned.clone(), normalized.clone()), application);
        let frame_count = arena.frames.len();
        for _ in 0..20 {
            assert_eq!(arena.applied(aligned.clone(), recursive_arguments.clone()), application);
            assert_eq!(arena.rebind(wrapped_application, &identity), application);
        }
        assert_eq!(
            arena.frames.len(),
            frame_count,
            "normalization keys contents, never predecessor history"
        );
    }

    #[test]
    fn ordered_observed_rows_and_source_vocabularies_are_part_of_frame_identity() {
        let mut types = Types::new();
        let source = activation(&mut types, 0, 2);
        let mut arena = FrameArena::<u32>::default();
        let first = arena.observed_row(source.clone(), vec![1, 2]);
        let second = arena.observed_row(source.clone(), vec![2, 1]);
        assert_ne!(first, second);
        assert_eq!(first, arena.observed_row(source.clone(), vec![1, 2]));
        let inputs = arena.identity(first);
        let applied = arena.applied(source, inputs.clone());
        let other_source = activation(&mut types, 1, 2);
        let other_vocabulary = arena.applied(other_source, inputs.clone());
        assert_ne!(applied, other_vocabulary);
        assert_eq!(arena.rebind(applied, &inputs), applied);
        let reversed = Substitution {
            arguments: inputs.arguments.iter().rev().cloned().collect(),
        };
        assert_ne!(arena.rebind(applied, &reversed), applied);
        assert!(
            arena.input(first, 0).is_none(),
            "an observed port is read as evidence, not unfolded as a source row"
        );
    }

    #[test]
    fn derived_proof_observations_preserve_original_source_ports_without_predecessor_frames() {
        let mut types = Types::new();
        let source = activation(&mut types, 0, 2);
        let mut arena = FrameArena::<u32>::default();
        let family = arena.family(source.clone());
        let evidence = arena.observed_row(source.clone(), vec![99, 99]);
        let origin = BoundSkeleton::new(evidence, Skeleton::Input(0));
        let first = arena.derived_observation(origin.clone(), 99);
        let other_slot = arena.derived_observation(BoundSkeleton::new(evidence, Skeleton::Input(1)), 99);
        let ground = arena.derived_observation(BoundSkeleton::new(family, Skeleton::Ground(ValueId::from_u32(0))), 99);
        let result = arena.derived_observation(
            BoundSkeleton::new(
                family,
                Skeleton::Result {
                    callsite: crate::compiler2::body::CallSiteId::from_u32(0),
                    value: ValueId::from_u32(0),
                },
            ),
            99,
        );
        assert_ne!(first, other_slot);
        assert_ne!(first, ground);
        assert_ne!(ground, result);
        assert_eq!(arena.derived_origin(first), Some(&origin));
        assert_eq!(arena.source(first), &source);
        assert_eq!(arena.observation(first, 0), Some(&99));
        assert_eq!(
            arena.identity(first).arguments.len(),
            1,
            "a proof coordinate is not the source's formal input row"
        );
        assert_eq!(
            arena.derived_observation(BoundSkeleton::new(first, Skeleton::Input(0)), 99),
            first
        );
        let projected = BoundSkeleton::new(first, Skeleton::project(Skeleton::Input(0), ProjectStep::ListTail));
        assert_eq!(arena.derived_observation(projected, 99), first);
        assert_ne!(
            arena.derived_observation(BoundSkeleton::new(first, Skeleton::Input(0)), 100),
            first
        );
        let zero_arity = activation(&mut types, 1, 0);
        let zero_family = arena.family(zero_arity.clone());
        let zero_value = arena.derived_observation(
            BoundSkeleton::new(zero_family, Skeleton::Ground(ValueId::from_u32(0))),
            99,
        );
        assert_eq!(arena.identity(zero_value).arguments.len(), 1);
        assert_eq!(arena.source(zero_value), &zero_arity);
        assert_ne!(zero_value, ground);
    }
}
