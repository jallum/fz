use std::borrow::Cow;

use crate::ast::{Pattern, Spanned};
use crate::dispatch_matrix::pattern::{
    PatternBodyId, PatternDispatchError, PatternDispatchPlan, PatternRow, PatternSubjectRef, SourcePatternRows,
    pattern_dispatch_from_source,
};
use crate::source::Span;

use super::semantic::{CallSiteSummary, CallTargetSummary, CallableFlowEdge};
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
    let arrived = arrival_order(types, &summary.targets);
    let (targets, observable_inputs) = routable_alternatives(types, &arrived);
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
    let groups = question_groups(types, targets);
    let unroutable = unroutable_alternatives(types, targets, &observable_inputs, &groups);
    targets
        .iter()
        .cloned()
        .zip(observable_inputs)
        .enumerate()
        .filter(|(index, _)| !unroutable.contains(index))
        .map(|(_, alternative)| alternative)
        .unzip()
}

/// The partition of a callsite's targets by the question their observable
/// surfaces project to.
///
/// One group is one question: every member asks the runtime the same thing of
/// every input, so no emitted test separates them and whichever member the
/// graph reaches first receives every value the group can see. A group of size
/// one is a real choice; a group of size two or more is a choice the plan
/// cannot make.
///
/// Neither the observable surface nor the question is the settled semantic
/// surface. `runtime_type_test_envelope` erases what no runtime test can look
/// at -- a callable's arrow and captures go, its IDENTITY stays, because the
/// value's own heap word names the code it was minted from -- and
/// `RuntimeTypePredicate` is coarser again: `{:cont, pair}` and
/// `{:cont | :halt, pair}` both project to "a 2-tuple".
pub(crate) fn question_groups(types: &mut Types, targets: &[CallTargetSummary]) -> Vec<Vec<usize>> {
    let questions = targets
        .iter()
        .map(|target| {
            runtime_dispatch_inputs(types, &target.surface_inputs)
                .iter()
                .map(|ty| types.runtime_type_predicate(ty))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut groups = Vec::new();
    let mut grouped = vec![false; targets.len()];
    for index in 0..targets.len() {
        if grouped[index] {
            continue;
        }
        let group = (index..targets.len())
            .filter(|other| questions[*other] == questions[index])
            .collect::<Vec<_>>();
        for slot in &group {
            grouped[*slot] = true;
        }
        groups.push(group);
    }
    groups
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

/// The alternatives no runtime test could ever route to: each accepts strictly
/// less than a sibling the runtime cannot tell it apart from.
///
/// Such an alternative is never a real choice. Placed after its wider twin it
/// is dead; placed before it, it swallows the twin's values and runs the wrong
/// body -- so arm order, which is the scheduler's and not the language's,
/// would decide the program's meaning. Dropping it sends those values to the
/// wider twin, which `stands_in_for` proves is complete for them.
///
/// `stands_in_for` is judged on OBSERVABLE surfaces, not settled semantic ones
/// (fz-kdt.118), and its same-callee half is load-bearing: a multi-target
/// callsite normally names one target per SELECTED CALLEE -- that is what
/// protocol dispatch is (`jobs/semantic.rs` settles one `CallTargetSummary`
/// per viable impl) -- and a wider domain sitting on another function's body is
/// no stand-in at all.
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
/// apart rather than a smaller plan (fz-kdt.107). The callable axis is one such
/// cure: two arms that differ only in which lambda they were keyed on are no
/// longer one question at all (fz-kdt.125), so they never reach this rule.
fn unroutable_alternatives(
    types: &Types,
    targets: &[CallTargetSummary],
    observable: &[Vec<Ty>],
    groups: &[Vec<usize>],
) -> Vec<usize> {
    let stands_in_for = |wide: usize, narrow: usize| {
        targets[wide].callee == targets[narrow].callee
            && observable[wide].len() == observable[narrow].len()
            && observable[wide]
                .iter()
                .zip(&observable[narrow])
                .all(|(wide, narrow)| types.is_subtype(narrow, wide))
    };
    groups
        .iter()
        .flat_map(|group| {
            group.iter().copied().filter(|narrow| {
                group
                    .iter()
                    .copied()
                    .any(|wide| wide != *narrow && stands_in_for(wide, *narrow) && !stands_in_for(*narrow, wide))
            })
        })
        .collect()
}

/// The order a callsite's settled targets arrive in.
///
/// Arm order is the scheduler's, never the language's: any permutation of a
/// callsite's targets is an order the semantic fixpoint could legally have
/// produced. Production reads the settled order and borrows it; the stress
/// gate reverses each runtime-indistinguishable group, which is the one
/// permutation that flips which member of a group the plan's identical rows
/// resolve to. A behavior that moves under it is a behavior arm order decides.
fn arrival_order<'a>(types: &mut Types, targets: &'a [CallTargetSummary]) -> Cow<'a, [CallTargetSummary]> {
    if !arm_order_stress::reversing() {
        return Cow::Borrowed(targets);
    }
    Cow::Owned(arm_order_stress::reverse_indistinguishable_groups(types, targets))
}

/// The schedule-legal perturbation the arm-order stress gate drives with.
///
/// Reversing a runtime-indistinguishable group permutes only arms no runtime
/// test can separate, so every order it produces is one the fixpoint could
/// have delivered on its own.
///
/// The setting is per-thread. A process-wide default comes from
/// `REVERSE_ARM_ORDER_ENV`, which is how a fixture gets swept through the real
/// `fz2` binary; in-process drivers install [`ReversedArmOrder`] instead, and
/// because each `cargo test` case owns its thread the perturbation never leaks
/// into a neighbour running beside it.
pub(crate) mod arm_order_stress {
    use std::cell::Cell;

    use super::{CallTargetSummary, Types, question_groups};

    /// Names the environment variable that turns the perturbation on for a
    /// whole process, so a fixture can be swept through the real `fz2` binary
    /// as well as driven in-process.
    pub(crate) const REVERSE_ARM_ORDER_ENV: &str = "FZ_STRESS_REVERSE_DISPATCH_ARMS";

    thread_local! {
        static REVERSING: Cell<bool> = Cell::new(matches!(
            std::env::var(REVERSE_ARM_ORDER_ENV).as_deref(),
            Ok(value) if !value.is_empty() && value != "0"
        ));
    }

    pub(crate) fn reversing() -> bool {
        REVERSING.with(Cell::get)
    }

    /// Reverses each runtime-indistinguishable arm group for as long as it
    /// lives, then puts the previous setting back.
    #[cfg(test)]
    pub(crate) struct ReversedArmOrder(bool);

    #[cfg(test)]
    impl ReversedArmOrder {
        pub(crate) fn install() -> Self {
            Self(REVERSING.with(|reversing| reversing.replace(true)))
        }
    }

    #[cfg(test)]
    impl Drop for ReversedArmOrder {
        fn drop(&mut self) {
            REVERSING.with(|reversing| reversing.set(self.0));
        }
    }

    /// The same targets, with the members of each group that asks one runtime
    /// question mirrored across the slots that group already occupies.
    pub(crate) fn reverse_indistinguishable_groups(
        types: &mut Types,
        targets: &[CallTargetSummary],
    ) -> Vec<CallTargetSummary> {
        let mut reversed = targets.to_vec();
        for group in question_groups(types, targets) {
            for (slot, source) in group.iter().zip(group.iter().rev()) {
                reversed[*slot] = targets[*source].clone();
            }
        }
        reversed
    }
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
    use crate::dispatch_matrix::{DispatchNode, Region, SubjectId, SubjectSource};
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

    /// fz-kdt.125: the reducer literal is the answer, not the problem.
    ///
    /// This is the shape `Range.reduce_step/6` really settles: the wide arm is
    /// `({:cont, int} | {:halt, int}, #66closure[])` and the narrow one is
    /// `({:cont, int}, #68closure[])`. The state column is one question --
    /// both are "a 2-tuple" -- and fz-kdt.118 read the reducer column as no
    /// question at all, so the pair collapsed to its wider half and `{:halt, 3}`
    /// was kept safe by having nowhere else to go.
    ///
    /// It is a question. A closure value's heap word names the lambda it was
    /// minted from, so these are two destinations the runtime can tell apart,
    /// each reached only by the values it was keyed on -- and `{:halt, 3}` now
    /// reaches the arm that handles it because the reducer it travelled with
    /// says so, not because its alternative was deleted.
    #[test]
    fn a_closure_literal_tells_two_indistinguishable_states_apart() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let cont_atom = world.types_mut().atom_lit("cont");
        let halt_atom = world.types_mut().atom_lit("halt");
        let cont = world.types_mut().tuple(&[cont_atom, int]);
        let halt = world.types_mut().tuple(&[halt_atom, int]);
        let command = world.types_mut().union(cont, halt);
        let halting_reducer = world.types_mut().closure_lit(ClosureTarget(66), Vec::new(), 2);
        let plain_reducer = world.types_mut().closure_lit(ClosureTarget(68), Vec::new(), 2);
        let step = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "reduce_step", 2);
        let target = |state, reducer| CallTargetSummary {
            callee: SelectedCallee::Function(step),
            surface_inputs: vec![state, reducer],
            activation: None,
            activation_inputs: None,
            return_ty: None,
        };
        let summary = CallSiteSummary {
            targets: vec![target(command, halting_reducer), target(cont, plain_reducer)],
            return_ty: None,
        };

        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("two reducers the runtime can name are two destinations");
        };

        assert_eq!(
            dispatch.targets, summary.targets,
            "neither arm stands in for the other once the reducer column is a real question",
        );
        assert!(
            dispatch.plan.matrix.arms.iter().all(|arm| arm
                .questions
                .iter()
                .any(|question| question.predicate.subject == SubjectId(1))),
            "every arm must ask which reducer arrived: {:#?}",
            dispatch.plan.matrix.arms,
        );
    }

    /// fz-kdt.125's headline, at the callsite that produced it: two arms alike
    /// in everything but which lambda they were keyed on.
    ///
    /// `Pipeline.run/2` forwards its callable, so one generalized body serves
    /// both lambdas and its one callsite names both specializations of
    /// `apply_twice/2`. Before the callable axis the plan asked nothing, arm 0
    /// received every value the group could see, and `n * 3` never ran. The
    /// arms are separable, and by the only thing that distinguishes them.
    #[test]
    fn arms_that_differ_only_in_their_lambda_are_told_apart_by_it() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let one_reducer = world.types_mut().closure_lit(ClosureTarget(66), Vec::new(), 2);
        let other_reducer = world.types_mut().closure_lit(ClosureTarget(68), Vec::new(), 2);
        let apply = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "apply_twice", 2);
        let target = |reducer| CallTargetSummary {
            callee: SelectedCallee::Function(apply),
            surface_inputs: vec![int, reducer],
            activation: None,
            activation_inputs: None,
            return_ty: None,
        };
        let summary = CallSiteSummary {
            targets: vec![target(one_reducer), target(other_reducer)],
            return_ty: None,
        };

        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("two lambdas the runtime can name are two destinations");
        };
        assert_eq!(
            dispatch.targets, summary.targets,
            "both arms stay, and now each is reachable",
        );
        assert!(
            matches!(
                dispatch.plan.graph.node(dispatch.plan.graph.root),
                Some(DispatchNode::Test { .. })
            ),
            "the plan must ask which lambda arrived rather than resolve unconditionally",
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

    /// fz-kdt.125: the callable-flow bridge dispatches on callable identity
    /// too. Two members reached by two different lambdas are two runtime
    /// questions, and semantic reachability agrees with the routing the plan
    /// emits rather than with source order.
    #[test]
    fn callable_flow_dispatch_discriminates_callable_correlations() {
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
        assert_ne!(
            world.types().runtime_type_predicate(&closure_a),
            world.types().runtime_type_predicate(&closure_b),
            "distinct callables are distinct runtime-observable predicates",
        );
        assert!(
            plan.matrix.arms.iter().all(|arm| !arm.questions.is_empty()),
            "callable-flow dispatch must ask which callable arrived",
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
            vec![1],
            "the member keyed on the callable that arrived is the one that runs",
        );
    }
}
