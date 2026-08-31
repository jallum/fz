use crate::ast::{Pattern, Spanned};
use crate::dispatch_matrix::pattern::{
    PatternBodyId, PatternDispatchError, PatternDispatchPlan, PatternRow, PatternSubjectRef, SourcePatternRows,
    pattern_dispatch_from_source,
};
use crate::runtime_type_predicate::RuntimeTypePredicate;
use crate::source::Span;

use super::semantic::{CallSiteSummary, CallTargetSummary, CallableFlowEdge, SelectedCallee};
use super::types::{Ty, Types};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallSiteDispatch {
    pub(crate) plan: PatternDispatchPlan<Ty>,
    pub(crate) targets: Vec<CallTargetSummary>,
    pub(crate) arm_body_ids: Vec<u32>,
}

/// What a callsite's settled targets amount to once the runtime's power to
/// tell them apart is accounted for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CallDestinations {
    /// The callsite named no target it could reach.
    None,
    /// One destination: an ordinary direct call, never a one-armed dispatch.
    Direct(CallTargetSummary),
    /// Several the runtime can tell apart: a dispatch over all of them.
    Dispatch(Box<CallSiteDispatch>),
}

/// The destinations a callsite can actually route to.
///
/// A callsite names one target per specialization the analysis settled, but a
/// call can only offer as many destinations as the runtime can tell apart:
/// `unroutable_alternatives` names the ones no runtime test could ever choose,
/// and dropping them here is what keeps arm order out of the language's
/// semantics.
pub(crate) fn call_destinations(
    types: &mut Types,
    summary: &CallSiteSummary,
) -> Result<CallDestinations, PatternDispatchError> {
    if summary.targets.len() <= 1 {
        return Ok(sole_destination(summary.targets.first().cloned()));
    }
    let arity = summary.arity();
    let (targets, observable_inputs) = routable_alternatives(types, &summary.targets);
    if targets.len() <= 1 {
        return Ok(sole_destination(targets.into_iter().next()));
    }
    let discriminating_inputs = discriminating_inputs(arity, observable_inputs.iter().map(Vec::as_slice));
    let rows = observable_inputs
        .into_iter()
        .enumerate()
        .map(|(index, inputs)| dispatch_row(&inputs, arity, &discriminating_inputs, index as PatternBodyId))
        .collect::<Vec<_>>();
    let plan = pattern_dispatch_from_source(SourcePatternRows {
        input_count: arity,
        rows,
    })?;
    let arm_body_ids = (0..targets.len() as u32).collect();
    Ok(CallDestinations::Dispatch(Box::new(CallSiteDispatch {
        plan,
        targets,
        arm_body_ids,
    })))
}

/// A callsite with no choice left to make.
fn sole_destination(target: Option<CallTargetSummary>) -> CallDestinations {
    match target {
        Some(target) => CallDestinations::Direct(target),
        None => CallDestinations::None,
    }
}

/// The routable targets among two or more, each paired with the widened
/// surface its runtime questions are asked about.
fn routable_alternatives(types: &mut Types, targets: &[CallTargetSummary]) -> (Vec<CallTargetSummary>, Vec<Vec<Ty>>) {
    let observable_inputs = targets
        .iter()
        .map(|target| runtime_dispatch_inputs(types, &target.surface_inputs))
        .collect::<Vec<_>>();
    let unroutable = {
        let alternatives = targets
            .iter()
            .zip(&observable_inputs)
            .map(|(target, observable)| DispatchAlternative::new(types, target, observable))
            .collect::<Vec<_>>();
        unroutable_alternatives(types, &alternatives)
    };
    targets
        .iter()
        .cloned()
        .zip(observable_inputs)
        .enumerate()
        .filter(|(index, _)| !unroutable.contains(index))
        .map(|(_, alternative)| alternative)
        .unzip()
}

pub(crate) fn dispatch_from_callable_flow_edges(
    types: &mut Types,
    edges: &[CallableFlowEdge],
) -> Result<Option<PatternDispatchPlan<Ty>>, PatternDispatchError> {
    if edges.len() <= 1 {
        return Ok(None);
    }
    let arity = edges[0].surface.inputs.len();
    let observable_inputs = edges
        .iter()
        .map(|edge| runtime_dispatch_inputs(types, &edge.surface.inputs))
        .collect::<Vec<_>>();
    let discriminating_inputs = discriminating_inputs(arity, observable_inputs.iter().map(Vec::as_slice));
    let rows = observable_inputs
        .into_iter()
        .enumerate()
        .map(|(index, inputs)| PatternRow {
            patterns: (0..arity)
                .map(|_| Spanned::new(Pattern::Wildcard, Span::DUMMY))
                .collect(),
            preconditions: discriminating_inputs
                .iter()
                .map(|input| (PatternSubjectRef::Input(*input as u32), inputs[*input]))
                .collect(),
            guard: None,
            body_id: index as PatternBodyId,
        })
        .collect::<Vec<_>>();
    pattern_dispatch_from_source(SourcePatternRows {
        input_count: arity,
        rows,
    })
    .map(Some)
}

/// One candidate destination of a dispatch: the semantic call surface the
/// analysis settled for the target, beside the runtime questions that surface
/// actually projects to.
///
/// The two are not the same information. A `Region::Type` question is answered
/// at runtime through `RuntimeTypePredicate`, which is coarser than the type it
/// is projected from: `{:cont, pair}` and `{:cont | :halt, pair}` both project
/// to "a 2-tuple".
struct DispatchAlternative<'a> {
    callee: &'a SelectedCallee,
    semantic: &'a [Ty],
    questions: Vec<RuntimeTypePredicate>,
}

impl<'a> DispatchAlternative<'a> {
    fn new(types: &Types, target: &'a CallTargetSummary, observable: &[Ty]) -> Self {
        Self {
            callee: &target.callee,
            semantic: &target.surface_inputs,
            questions: observable.iter().map(|ty| types.runtime_type_predicate(ty)).collect(),
        }
    }

    /// No runtime test can tell this alternative from `other`: the two
    /// surfaces project to the same questions.
    ///
    /// One-way containment is NOT this relation. When the questions differ,
    /// the narrower test matches only values its own domain names and
    /// everything else falls through, so whichever order the two are tested
    /// in, a value the pair can see lands in an arm whose domain contains it:
    /// order costs precision, not meaning. When the questions are the SAME,
    /// the narrower arm also matches values its domain does NOT contain, and
    /// no order-independent reading survives. That is the defect.
    fn runtime_indistinguishable(&self, other: &Self) -> bool {
        self.questions == other.questions
    }

    /// This alternative's body is complete for everything `other` accepts: it
    /// is the SAME function, specialized on a domain that contains `other`'s.
    ///
    /// Both halves are load-bearing, and domain containment alone is NOT
    /// behavioral completeness. A multi-target callsite normally names one
    /// target per SELECTED CALLEE -- that is what protocol dispatch is
    /// (`jobs/semantic.rs` settles one `CallTargetSummary` per viable impl) --
    /// and a wider domain sitting on another function's body is no stand-in
    /// at all. Rerouting a narrow domain into it would be a miscompile however
    /// neatly the types line up.
    fn stands_in_for(&self, types: &Types, other: &Self) -> bool {
        self.callee == other.callee
            && self.semantic.len() == other.semantic.len()
            && self
                .semantic
                .iter()
                .zip(other.semantic)
                .all(|(wide, narrow)| types.is_subtype(narrow, wide))
    }
}

/// The alternatives no runtime test could ever route to: each accepts strictly
/// less than a sibling the runtime cannot tell it apart from.
///
/// Such an alternative is never a real choice. Placed after its wider twin it
/// is dead; placed before it, it swallows the twin's values and runs the wrong
/// body -- so arm order, which is the scheduler's and not the language's,
/// would decide the program's meaning. Dropping it sends those values to the
/// wider twin, which `stands_in_for` proves is complete for them.
///
/// Strictness is what makes the relation antisymmetric: alternatives of equal
/// denotation are never each other's excuse for disappearing. Both halves are
/// transitive, so an alternative dropped only because of another dropped one
/// is dropped by that one's own twin too, and no cascade is needed.
///
/// Twins with no stand-in between them -- neither's domain contains the
/// other's, or they are different functions entirely -- are left alone:
/// dropping either would lose a body nothing else can supply. Those callsites
/// stay order-decided, and the cure is a runtime predicate that can tell them
/// apart rather than a smaller plan (fz-kdt.107).
fn unroutable_alternatives(types: &Types, alternatives: &[DispatchAlternative<'_>]) -> Vec<usize> {
    (0..alternatives.len())
        .filter(|index| {
            let narrow = &alternatives[*index];
            alternatives.iter().enumerate().any(|(other, wide)| {
                other != *index
                    && wide.runtime_indistinguishable(narrow)
                    && wide.stands_in_for(types, narrow)
                    && !narrow.stands_in_for(types, wide)
            })
        })
        .collect()
}

fn runtime_dispatch_inputs(types: &mut Types, inputs: &[Ty]) -> Vec<Ty> {
    inputs
        .iter()
        .copied()
        .map(|input| types.runtime_type_test_envelope(input))
        .collect()
}

fn discriminating_inputs<'a>(arity: usize, inputs: impl Iterator<Item = &'a [Ty]>) -> Vec<usize> {
    let inputs = inputs.collect::<Vec<_>>();
    let Some(first) = inputs.first() else {
        return Vec::new();
    };
    (0..arity)
        .filter(|index| inputs.iter().skip(1).any(|input| input[*index] != first[*index]))
        .collect()
}

fn dispatch_row(
    observable_inputs: &[Ty],
    arity: usize,
    discriminating_inputs: &[usize],
    body_id: PatternBodyId,
) -> PatternRow<Ty> {
    let mut patterns = Vec::with_capacity(arity);
    patterns.resize_with(arity, || Spanned::new(Pattern::Wildcard, Span::DUMMY));
    PatternRow {
        patterns,
        preconditions: discriminating_inputs
            .iter()
            .map(|input| (PatternSubjectRef::Input(*input as u32), observable_inputs[*input]))
            .collect(),
        guard: None,
        body_id,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::dispatch_reachability::calculate_dispatch_reachability;
    use crate::compiler2::types::ClosureTarget;
    use crate::compiler2::{SelectedCallee, World};
    use crate::dispatch_matrix::{DispatchNode, Region, SubjectSource};
    use crate::telemetry::ConfiguredTelemetry;

    #[test]
    fn multi_target_summary_builds_receiver_type_dispatch_rows() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let list_impl = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "list_impl", 1);
        let range_impl = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "range_impl", 1);
        let any = world.types_mut().any();
        let list = world.types_mut().list(any);
        let range = world.types_mut().opaque_of("impl-target::Range");
        let summary = CallSiteSummary {
            targets: vec![
                CallTargetSummary {
                    callee: SelectedCallee::Function(list_impl),
                    surface_inputs: vec![list],
                    activation: None,
                    activation_inputs: None,
                    return_ty: None,
                },
                CallTargetSummary {
                    callee: SelectedCallee::Function(range_impl),
                    surface_inputs: vec![range],
                    activation: None,
                    activation_inputs: None,
                    return_ty: None,
                },
            ],
            return_ty: None,
        };

        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("dispatch should compile")
        else {
            panic!("multi-target summary should dispatch");
        };

        assert_eq!(dispatch.targets, summary.targets);
        assert_eq!(dispatch.plan.input_count, 1);
        assert_eq!(
            dispatch.plan.matrix.subjects.first().map(|subject| &subject.source),
            Some(&SubjectSource::Input { ordinal: 0 }),
            "callsite dispatch should test the receiver input"
        );
        assert_eq!(
            dispatch
                .plan
                .outcomes
                .iter()
                .map(|outcome| outcome.body_id)
                .collect::<Vec<_>>(),
            vec![0, 1],
            "body ids should stay parallel to summary targets"
        );
        let type_regions = dispatch
            .plan
            .matrix
            .arms
            .iter()
            .map(|arm| {
                arm.questions
                    .iter()
                    .find_map(|question| match question.predicate.region {
                        Region::Type(ty) => Some(ty),
                        _ => None,
                    })
                    .expect("each callsite dispatch arm should type-test the receiver")
            })
            .collect::<Vec<_>>();
        assert_eq!(type_regions, vec![list, range]);
        assert!(
            matches!(
                dispatch.plan.graph.node(dispatch.plan.graph.root),
                Some(DispatchNode::Test { .. })
            ),
            "multi-target callsite dispatch should compile to a real decision graph"
        );
    }

    #[test]
    fn single_target_summary_stays_direct() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "impl", 1);
        let any = world.types_mut().any();
        let summary = CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(function),
                surface_inputs: vec![any],
                activation: None,
                activation_inputs: None,
                return_ty: None,
            }],
            return_ty: None,
        };

        assert!(
            matches!(
                call_destinations(world.types_mut(), &summary).expect("single target should not fail"),
                CallDestinations::Direct(_)
            ),
            "single-target callsites must remain ordinary direct calls"
        );
    }

    /// fz-kdt.104: `{:cont, pair}` and `{:cont | :halt, pair}` are one question
    /// to the runtime -- both are just "a 2-tuple". Offering both as arms would
    /// make arm order, which is the scheduler's, decide whether `:halt` ever
    /// halts. The wider one alone is the destination, and a callsite with one
    /// destination is a direct call.
    #[test]
    fn a_narrower_twin_of_an_indistinguishable_arm_is_no_destination() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let list = world.types_mut().list(int);
        let pair = world.types_mut().tuple(&[list, int]);
        let cont_atom = world.types_mut().atom_lit("cont");
        let halt_atom = world.types_mut().atom_lit("halt");
        let cont = world.types_mut().tuple(&[cont_atom, pair]);
        let halt = world.types_mut().tuple(&[halt_atom, pair]);
        let command = world.types_mut().union(cont, halt);
        let step = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "reduce_while_step", 2);
        let target = |state| CallTargetSummary {
            callee: SelectedCallee::Function(step),
            surface_inputs: vec![list, state],
            activation: None,
            activation_inputs: None,
            return_ty: None,
        };
        let summary = CallSiteSummary {
            targets: vec![target(command), target(cont)],
            return_ty: None,
        };

        let destinations = call_destinations(world.types_mut(), &summary).expect("destinations should compile");

        assert_eq!(
            destinations,
            CallDestinations::Direct(target(command)),
            "the narrow `{{:cont, _}}` twin is not an alternative the runtime could route to",
        );
    }

    /// fz-kdt.104 (refuter finding): the drop is only sound between
    /// specializations of ONE source function. Here two DIFFERENT functions
    /// are named for domains that are subtype-related and project to one
    /// runtime question -- exactly the shape the pairwise rule would otherwise
    /// collapse. Rerouting `Narrow`'s domain into `Wide`'s body would run the
    /// wrong function, so both destinations stay and the callsite keeps its
    /// dispatch.
    #[test]
    fn a_wider_domain_on_another_function_is_no_stand_in() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let list = world.types_mut().list(int);
        let pair = world.types_mut().tuple(&[list, int]);
        let cont_atom = world.types_mut().atom_lit("cont");
        let halt_atom = world.types_mut().atom_lit("halt");
        let cont = world.types_mut().tuple(&[cont_atom, pair]);
        let halt = world.types_mut().tuple(&[halt_atom, pair]);
        let command = world.types_mut().union(cont, halt);
        let wide_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "wide_impl", 2);
        let narrow_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "narrow_impl", 2);
        let target = |function, state| CallTargetSummary {
            callee: SelectedCallee::Function(function),
            surface_inputs: vec![list, state],
            activation: None,
            activation_inputs: None,
            return_ty: None,
        };
        let summary = CallSiteSummary {
            targets: vec![target(wide_fn, command), target(narrow_fn, cont)],
            return_ty: None,
        };

        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("two functions are two destinations, however their domains nest");
        };
        assert_eq!(
            dispatch.targets, summary.targets,
            "a domain that contains another's is not a stand-in for another function's body",
        );
    }

    /// The other side of the same rule. `:timeout` beside `any` is a real
    /// specialization: the runtime CAN tell an atom from everything else, so
    /// the narrow test matches only values its own domain names and the rest
    /// fall through. Whichever order they are tested in, every value lands in
    /// an arm whose domain contains it -- order costs precision here, not
    /// meaning -- so both arms stay.
    #[test]
    fn a_narrower_arm_the_runtime_can_still_recognize_stays() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let any = world.types_mut().any();
        let timeout = world.types_mut().atom_lit("timeout");
        let bump = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "bump", 1);
        let target = |input| CallTargetSummary {
            callee: SelectedCallee::Function(bump),
            surface_inputs: vec![input],
            activation: None,
            activation_inputs: None,
            return_ty: None,
        };
        let summary = CallSiteSummary {
            targets: vec![target(any), target(timeout)],
            return_ty: None,
        };

        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("a recognizable narrow arm must survive as a dispatch alternative");
        };
        assert_eq!(
            dispatch.targets, summary.targets,
            "both arms ask questions the runtime can tell apart",
        );
    }

    #[test]
    fn callsite_summary_dispatches_on_the_surface_argument_that_distinguishes_targets() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let cont = world.types_mut().atom();
        let halt = world.types_mut().tuple(&[int]);
        let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "step", 2);
        let summary = CallSiteSummary {
            targets: vec![
                CallTargetSummary {
                    callee: SelectedCallee::Function(function),
                    surface_inputs: vec![int, cont],
                    activation: None,
                    activation_inputs: None,
                    return_ty: None,
                },
                CallTargetSummary {
                    callee: SelectedCallee::Function(function),
                    surface_inputs: vec![int, halt],
                    activation: None,
                    activation_inputs: None,
                    return_ty: None,
                },
            ],
            return_ty: None,
        };

        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("dispatch should compile")
        else {
            panic!("distinct targets require dispatch");
        };

        assert!(
            dispatch
                .plan
                .matrix
                .subjects
                .iter()
                .any(|subject| subject.source == SubjectSource::Input { ordinal: 1 }),
            "the callsite must discriminate its command argument, not its shared first argument"
        );
    }

    #[test]
    fn callable_flow_dispatches_on_the_surface_argument_that_distinguishes_members() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();
        let tuple = world.types_mut().tuple(&[int]);
        let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "lambda", 2);
        let mut edge = |state| CallableFlowEdge {
            surface: super::super::semantic::CallableSurface {
                inputs: vec![int, state],
            },
            resolution: super::super::identity::ExecutableKey {
                activation: super::super::identity::ActivationKey::from_inputs(
                    crate::compiler2::RootId::for_test(0),
                    function,
                    &[int, state],
                    world.types_mut(),
                ),
                need: crate::compiler2::ExecutableNeed::Value,
            },
            capture_semantic_inputs: Box::default(),
            surface_semantic_inputs: Box::from([0, 1]),
        };

        let edges = [edge(atom), edge(tuple)];
        let dispatch = dispatch_from_callable_flow_edges(world.types_mut(), &edges)
            .expect("callable flow dispatch should compile")
            .expect("distinct callable members require dispatch");

        assert!(
            dispatch
                .matrix
                .subjects
                .iter()
                .any(|subject| subject.source == SubjectSource::Input { ordinal: 1 }),
            "the bridge must discriminate its state argument, not its shared entry argument"
        );
    }

    #[test]
    fn callable_flow_dispatch_does_not_discriminate_unobservable_callable_correlations() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let closure_a = world.types_mut().closure_lit(ClosureTarget(1), Vec::new(), 1);
        let closure_b = world.types_mut().closure_lit(ClosureTarget(2), Vec::new(), 1);
        let target_a = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "target_a", 1);
        let target_b = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "target_b", 1);
        let root = crate::compiler2::RootId::for_test(0);
        let edges = [
            CallableFlowEdge {
                surface: super::super::semantic::CallableSurface {
                    inputs: vec![closure_a],
                },
                resolution: super::super::identity::ExecutableKey {
                    activation: super::super::identity::ActivationKey::from_inputs(
                        root,
                        target_a,
                        &[closure_a],
                        world.types_mut(),
                    ),
                    need: crate::compiler2::ExecutableNeed::Value,
                },
                capture_semantic_inputs: Box::default(),
                surface_semantic_inputs: Box::from([0]),
            },
            CallableFlowEdge {
                surface: super::super::semantic::CallableSurface {
                    inputs: vec![closure_b],
                },
                resolution: super::super::identity::ExecutableKey {
                    activation: super::super::identity::ActivationKey::from_inputs(
                        root,
                        target_b,
                        &[closure_b],
                        world.types_mut(),
                    ),
                    need: crate::compiler2::ExecutableNeed::Value,
                },
                capture_semantic_inputs: Box::default(),
                surface_semantic_inputs: Box::from([0]),
            },
        ];
        let plan = dispatch_from_callable_flow_edges(world.types_mut(), &edges)
            .expect("callable flow dispatch should compile")
            .expect("distinct callable correlations should produce a plan");
        assert_eq!(
            world.types().runtime_type_predicate(&closure_a),
            world.types().runtime_type_predicate(&closure_b),
            "distinct callable correlations should have the same runtime-observable predicate",
        );
        assert!(
            plan.matrix.arms.iter().all(|arm| arm.questions.is_empty()),
            "callable-flow dispatch must not mint Region::Type questions for unobservable callable correlations",
        );
        let reachability = calculate_dispatch_reachability(world.types_mut(), &plan, &[closure_b]);
        let bodies = plan
            .outcomes
            .iter()
            .filter(|outcome| reachability.outcomes.contains(&outcome.outcome))
            .map(|outcome| outcome.body_id)
            .collect::<Vec<_>>();
        assert_eq!(
            bodies,
            vec![0],
            "semantic reachability must agree with the runtime's source-ordered selection",
        );
    }
}
