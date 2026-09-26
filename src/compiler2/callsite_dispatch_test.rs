//! What a plan asks, and in what order.

use super::*;
use crate::compiler2::dispatch_reachability::calculate_dispatch_reachability;
use crate::compiler2::types::ClosureTarget;
use crate::compiler2::{SelectedCallee, World};
use crate::dispatch_matrix::{DispatchNode, Region, RegionPredicate, SubjectId, SubjectSource};
use crate::telemetry::ConfiguredTelemetry;

/// The measured shape, written in atoms so the relations are the type
/// calculator's own and not a fixture's: two arms that OVERLAP at input 0 --
/// `:a` lies inside `:a | :b`, so no value there is turned away by the other
/// arm's question -- and SEPARATE at input 1, where `:x` and `:y` share no
/// value.
///
/// `List.reduce_while_step/3`'s `delivered_resume` selection is this pair:
/// `{:cont, {[int], int}}` inside `{:cont | :halt, {[int], int}}` at the
/// accumulator, two disjoint closure sets at the reducer.
struct OverlapThenSeparate {
    observable: Vec<Vec<Ty>>,
    questions: Vec<Vec<RuntimeTypePredicate>>,
    /// `[a, b, x, y]`.
    atoms: Vec<Ty>,
}

fn overlap_then_separate(world: &mut World) -> OverlapThenSeparate {
    let types = world.types_mut();
    let a = types.atom_lit("a");
    let b = types.atom_lit("b");
    let a_or_b = types.union(a, b);
    let x = types.atom_lit("x");
    let y = types.atom_lit("y");
    let surfaces = vec![vec![a, x], vec![a_or_b, y]];
    let observable = observable_inputs(types, &surfaces);
    let questions = runtime_questions(types, &observable);
    OverlapThenSeparate {
        observable,
        questions,
        atoms: vec![a, b, x, y],
    }
}

/// The plan asks the input that keeps the arms apart before the one that
/// cannot.
///
/// Input 0 is the narrower arm's whole reason for existing and input 1 is what
/// the runtime can actually decide between them on. Asked in input order the
/// plan leads with the question that admits both arms' values; asked in this
/// order it leads with the one that admits exactly one arm's.
#[test]
fn the_separating_input_is_asked_before_the_one_the_arms_only_overlap_at() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let pair = overlap_then_separate(&mut world);
    assert!(
        !separated_at(&pair.questions[0][0], &pair.questions[1][0]),
        "`:a` inside `:a | :b` is an overlap, so input 0 turns no value away",
    );
    assert!(
        separated_at(&pair.questions[0][1], &pair.questions[1][1]),
        "`:x` and `:y` share no value, so input 1 is what the plan's own test separates the arms by",
    );
    assert_eq!(
        dispatch_columns(2, &pair.observable, &pair.questions),
        vec![1, 0],
        "a separating input leads; the input the arms only overlap at follows it",
    );
}

/// A selection costs one question per arm the value walks through, in EITHER
/// seat -- which is what makes the seat of a separated pair a determinism
/// choice and nothing more.
///
/// Three values can reach this pair: `:a`/`:x` belongs to the `:a` arm, and
/// `:a`/`:y` and `:b`/`:y` to the `:a | :b` one. Asked in INPUT order the first
/// arm's question at input 0 admits a value the second arm owns -- `:a`/`:y`
/// answers it, is turned away by the separating question behind it, and then
/// answers the second arm's two, three matched questions where two were due.
/// Which value pays depends on the seat: input order costs [2, 3, 2] with the
/// `:a` arm first and [3, 2, 2] with the `:a | :b` arm first. Asked in column
/// order both seats cost two for every value, so the seat stops being visible.
#[test]
fn a_selection_costs_one_question_per_arm_in_either_seat() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let pair = overlap_then_separate(&mut world);
    let (a, b, x, y) = (pair.atoms[0], pair.atoms[1], pair.atoms[2], pair.atoms[3]);
    let values = [vec![a, x], vec![a, y], vec![b, y]];
    let columns = dispatch_columns(2, &pair.observable, &pair.questions);

    for seat in [vec![0, 1], vec![1, 0]] {
        let rows = seat
            .iter()
            .enumerate()
            .map(|(body, arm)| dispatch_row(&pair.observable[*arm], 2, &columns, body as PatternBodyId))
            .collect::<Vec<_>>();
        let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(2, rows)).expect("plan compiles");
        let matched = values
            .iter()
            .map(|value| matched_questions(world.types(), &plan, value))
            .collect::<Vec<_>>();
        assert_eq!(
            matched,
            vec![2, 2, 2],
            "with the arms seated {seat:?}, every value answers one question per arm it walks through",
        );
    }
}

/// How many questions a value answers YES to on its way through a plan -- the
/// quantity `SURFACE_MEMBERSHIP_CENSUS` counts on the production interpreter.
///
/// The arms here carry atoms at every input, and an atom test admits exactly
/// the atoms it names, so asking the calculator whether the value's type lies
/// inside the question's is asking what the emitted test asks.
fn matched_questions(types: &Types, plan: &PatternDispatchPlan<Ty>, value: &[Ty]) -> usize {
    let mut node = plan.graph.root;
    let mut matched = 0;
    loop {
        match plan.graph.node(node).expect("a plan's edges name its own nodes") {
            DispatchNode::Fail | DispatchNode::Outcome { .. } => return matched,
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let Region::Type(asked) = &predicate.region else {
                    panic!("this witness asks type questions only");
                };
                let held = value[input_ordinal(plan, predicate.subject)];
                node = if types.is_subtype(&held, asked) {
                    matched += 1;
                    on_match.target
                } else {
                    on_miss.target
                };
            }
        }
    }
}

/// The declared input a subject names. Every subject of a selection plan is one:
/// its rows are wildcards carrying preconditions, so nothing is projected.
fn input_ordinal(plan: &PatternDispatchPlan<Ty>, subject: SubjectId) -> usize {
    match &plan.graph.subjects[subject.0 as usize].source {
        SubjectSource::Input { ordinal } => *ordinal as usize,
        SubjectSource::Projection(_) => panic!("a selection plan projects nothing"),
    }
}

#[test]
fn multi_target_summary_builds_receiver_type_dispatch_rows() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let list_impl = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "list_impl", 1);
    let range_impl = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "range_impl", 1);
    let any = world.types_mut().any();
    let list = world.types_mut().list(any);
    let range = world
        .types_mut()
        .nominal_protocol_target(crate::modules::identity::ModuleName::from_segments(vec![
            "Range".into(),
        ]));
    let summary = CallSiteSummary {
        targets: vec![
            CallTargetSummary {
                callee: SelectedCallee::Function(list_impl),
                surface_inputs: vec![list],
                activation: None,
                activation_inputs: None,
                extern_params: None,
                return_ty: None,
            },
            CallTargetSummary {
                callee: SelectedCallee::Function(range_impl),
                surface_inputs: vec![range],
                activation: None,
                activation_inputs: None,
                extern_params: None,
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
        dispatch.plan.graph.subjects.first().map(|subject| &subject.source),
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
        .graph
        .nodes
        .iter()
        .filter_map(|node| match node {
            DispatchNode::Test {
                predicate:
                    RegionPredicate {
                        region: Region::Type(ty),
                        ..
                    },
                ..
            } => Some(*ty),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert!(type_regions.contains(&list) && type_regions.contains(&range));
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
            extern_params: None,
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

/// A narrow twin the plan CAN separate is still no destination when the
/// seat would not put it first.
///
/// `{:cont, pair}` and `{:cont | :halt, pair}` used to be one question --
/// both projected to "a 2-tuple" -- and fz-kdt.118 dropped the narrow twin
/// because nothing but arm order, which is the scheduler's, decided
/// whether `:halt` ever halted. fz-kdt.119 gave the tuple test a
/// sub-predicate per position, position 0 is an ATOM, and `{:cont}` and
/// `{:cont, :halt}` became two questions -- at which point 118's
/// group-local drop stopped reaching the pair and the callsite compiled to
/// a two-armed dispatch with the narrow arm seated second.
///
/// Seated second is DEAD, and this is the ticket that says so. The two
/// arms carry the SAME payload type, so they erasing-overlap through the
/// list head's unread tail (the one-sided-filter law -- heads equal, tails
/// erased), and only the wide arm's surface names everything the narrow
/// one's holds there. So `covering(narrow, wide)` is false, `seats_before`
/// declines to put the narrow arm ahead of the arm that stands in for it,
/// and the drop takes it: `Direct(wide)`, one destination, no plan.
///
/// Nothing is lost by that. `stands_in_for` proves the wide arm is the
/// same callee on a surface that contains the narrow one's, so it is
/// complete for every value the narrow arm could have received -- and the
/// arrival that seats the wide arm first is one the fixpoint could have
/// delivered, so this routing is one a legal arrival already produced.
#[test]
fn a_narrower_twin_the_seat_would_not_put_first_is_no_destination() {
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
        extern_params: None,
        return_ty: None,
    };

    for arrival in [vec![target(command), target(cont)], vec![target(cont), target(command)]] {
        let summary = CallSiteSummary {
            targets: arrival.clone(),
            return_ty: None,
        };
        let destinations = call_destinations(world.types_mut(), &summary).expect("destinations should compile");
        assert_eq!(
            destinations,
            CallDestinations::Direct(target(command)),
            "the narrow twin is seated second wherever it arrives, which is nowhere at all, so \
                 the callsite has one destination and makes no runtime choice",
        );
    }
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
        extern_params: None,
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

/// fz-kdt.118's own population, stated in one question so the
/// generalization can be read as the identity on it.
///
/// Two arms of ONE callee over maps with the same key at different value
/// types. A map test is a KIND check -- the axis is `Erasing`, because a
/// map value tells the runtime it is a map and nothing about what it holds
/// -- so `%{a: int}` and `%{a: int | float}` put one and the same question,
/// and the narrow surface is strictly inside the wide one.
///
/// Equal tests make `strictly_inside` false, so `seats_before` cannot put
/// the narrow arm ahead of the arm that stands in for it, and the drop
/// takes it. That is fz-kdt.118's rule exactly: where the two arms are one
/// question, the narrower is dropped for the wider twin of the same
/// callee. The rule this file now applies reaches further -- it is
/// quantified over every arm, not the members of one question group -- but
/// on 118's population it decides what 118 decided.
#[test]
fn a_map_content_no_test_can_read_leaves_only_the_wider_arm() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let float = world.types_mut().float();
    let ints_floats = world.types_mut().union(int, float);
    let key = crate::types::MapKey::Atom("a".to_string());
    let narrow_map = world.types_mut().map(&[(key.clone(), int)]);
    let wide_map = world.types_mut().map(&[(key, ints_floats)]);
    let read = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "read_a", 1);
    let target = |input| CallTargetSummary {
        callee: SelectedCallee::Function(read),
        surface_inputs: vec![input],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let narrow = target(narrow_map);
    let wide = target(wide_map);

    let questions = target_questions(world.types_mut(), &[narrow.clone(), wide.clone()]);
    assert_eq!(
        questions[0], questions[1],
        "the map axis reads nothing inside the map, so the two arms put one and the same \
             question -- which is the premise fz-kdt.118's drop was stated on",
    );

    for order in [[&narrow, &wide], [&wide, &narrow]] {
        let arrival = order.into_iter().cloned().collect::<Vec<_>>();
        let summary = CallSiteSummary {
            targets: arrival.clone(),
            return_ty: None,
        };
        let destinations = call_destinations(world.types_mut(), &summary).expect("destinations should compile");
        assert_eq!(
            destinations,
            CallDestinations::Direct(wide.clone()),
            "nothing the plan emits separates the two, so the narrow arm is no choice at all \
                 and the callsite is a direct call on the arm that stands in for it -- arrived \
                 {arrival:?}",
        );
    }
}

/// The precision boundary: the drop never takes an arm the seat would have
/// put first.
///
/// `int` and `int | float` on one callee. The narrow surface is strictly
/// inside the wide one and its test is inside the wide one's, so the wide
/// arm stands in for it -- but the numeric axes are SEPARATING: a value
/// that passes the `int` test is an int, which the narrow arm's surface
/// names, so neither arm can misread what the other's test admits.
/// `Covering` therefore holds both ways, the precision preference settles
/// it, and `seats_before(narrow, wide)` is TRUE.
///
/// So the narrow arm survives and is tested first: a value both tests
/// admit runs the body that named it most precisely (fz-kdt.129), and the
/// wide arm still receives everything the narrow test refuses. This is the
/// half of the rule that has no analogue in fz-kdt.118 -- 118 dropped on
/// stand-in alone, and stand-in alone would delete this specialization.
#[test]
fn a_narrower_arm_on_a_separating_axis_survives_and_is_seated_first() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let float = world.types_mut().float();
    let ints_floats = world.types_mut().union(int, float);
    let bump = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "bump", 1);
    let target = |input| CallTargetSummary {
        callee: SelectedCallee::Function(bump),
        surface_inputs: vec![input],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let narrow = target(int);
    let wide = target(ints_floats);

    for arrival in [vec![narrow.clone(), wide.clone()], vec![wide.clone(), narrow.clone()]] {
        let summary = CallSiteSummary {
            targets: arrival.clone(),
            return_ty: None,
        };
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("an int arm the runtime can recognize is a destination, arrived {arrival:?}");
        };
        assert_eq!(
            dispatch.targets,
            vec![narrow.clone(), wide.clone()],
            "an int passes the int test only by being an int, so the narrow arm can misread \
                 nothing and the seat puts it first -- which is exactly why the drop leaves it \
                 alone, arrived {arrival:?}",
        );
    }
}

/// Test containment is a SEPARATE conjunct from surface containment, and
/// this is the pair that proves it: the narrower SURFACE carries the WIDER
/// TEST.
///
/// `[int | :ok] & not([:ok])` is a strict subtype of `[int | :ok]` -- it
/// is that type with one clause carved out. But a negated list clause
/// cannot be projected to a head question, so the whole list axis degrades
/// to `ListShapes::shape_only`: the narrow arm asks "is it a list" where
/// its wide sibling asks "is it a list whose head is an int or `:ok`". The
/// narrow arm's test therefore admits `[:zzz]`, which the wide arm's
/// refuses.
///
/// The carve is rejoined with `[]` to reach that surface. Subtracting
/// `[:ok]` takes `[]` with it, and the list normal form reads that off the
/// clause, so the difference alone is a NON-EMPTY list type whose shape
/// question the wide arm's already refuses -- a second axis of difference,
/// which is not what this pair is for.
///
/// Drop it on surface containment alone and `[:zzz]` stops escaping into
/// the narrow arm and starts reaching the wide arm's body -- or the plan's
/// fail node -- which is an outcome no arrival of these two arms ever
/// produced. The relative-soundness theorem is only ever "every post-drop
/// routing is one a legal arrival produced", so an arm whose test admits
/// what its stand-in's refuses is not a redundant arm and is not dropped.
///
/// Both survive, and the seat is the wide arm first: their tests overlap
/// on the list axis, only the wide arm's surface names what the narrow
/// one's holds there, so coverage runs one way only.
#[test]
fn a_narrow_surface_carrying_the_wider_test_is_not_dropped_for_it() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok_atom = world.types_mut().atom_lit("ok");
    let ints_oks = world.types_mut().union(int, ok_atom);
    let ok_list = world.types_mut().list(ok_atom);
    let wide_list = world.types_mut().list(ints_oks);
    let carved = world.types_mut().difference(wide_list, ok_list);
    let empty_list = world.types_mut().empty_list();
    let narrow_list = world.types_mut().union(empty_list, carved);
    let step = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "reduce_while_step", 1);
    let target = |list| CallTargetSummary {
        callee: SelectedCallee::Function(step),
        surface_inputs: vec![list],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let narrow = target(narrow_list);
    let wide = target(wide_list);

    assert!(
        world.types_mut().is_subtype(&narrow_list, &wide_list) && narrow_list != wide_list,
        "the carved type must be a STRICT subtype, or the pair says nothing about the \
             conjunct under test",
    );
    let questions = target_questions(world.types_mut(), &[narrow.clone(), wide.clone()]);
    assert!(
        !questions[0][0].contained_in(&questions[1][0]) && questions[1][0].contained_in(&questions[0][0]),
        "the negated clause degrades the list axis to shape-only, so the narrower surface asks \
             the WIDER question -- which is what makes the test conjunct load-bearing rather than \
             implied by the surface one",
    );

    for arrival in [vec![narrow.clone(), wide.clone()], vec![wide.clone(), narrow.clone()]] {
        let summary = CallSiteSummary {
            targets: arrival.clone(),
            return_ty: None,
        };
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("an arm admitting values its sibling refuses is a destination, arrived {arrival:?}");
        };
        assert_eq!(
            dispatch.targets,
            vec![wide.clone(), narrow.clone()],
            "both arms survive because neither test is inside the other, and the covering arm \
                 is seated first -- arrived {arrival:?}",
        );
    }
}

/// The drop's residue, three arms wide: removing an arm DISSOLVES the
/// question group it belonged to, and the survivor that group pinned is
/// promoted past the arm which used to swallow its values.
///
/// The three arms, on one callsite:
///
/// ```text
///     N   impl_two   (%{a: int},         :a)
///     S   impl_zero  (%{a: int | float}, :a)
///     W   impl_two   (%{a: int | float}, :a | :c)
/// ```
///
/// A map test is a KIND check, so all three ask "is it a map" of input 0
/// and their atom sets of input 1: N and S put ONE question and W puts
/// another. With all three present the seat moves the group `{N, S}` as a
/// unit, and coverage quantifies over the product -- W's `%{a: int|float}`
/// is not inside N's `%{a: int}`, so the group cannot cover W, W covers the
/// group, and W is seated first on every one of the six arrivals. Nothing
/// the group holds ever reaches S: W's test admits every map at `:a`.
///
/// W stands in for N -- same callee, strictly wider surface, a test that
/// admits everything N's admits -- and `covering(N, W)` is false, so the drop
/// takes N. That is correct for N. What it also does is dissolve `{N, S}`:
/// S is judged alone, coverage runs both ways between S and W, S's test is
/// strictly inside W's, and the precision preference seats S FIRST. So
/// `(%{a: 1}, :a)` reaches `impl_zero` here and reached `impl_two` under
/// every arrival of the three arms.
///
/// It is not a blind escape: the seat only moves what it covers, so S's
/// surface names everything it now receives. It is a routing the drop
/// decides, and this gate is here so it cannot widen unnoticed. The
/// precondition -- a dropped arm sharing its question with a surviving one
/// -- occurs on no callsite in the corpus (swept over 597 fixtures at the
/// fz-kdt.143 landing: zero), and `unroutable_alternatives` states what
/// closing it would take.
#[test]
fn a_drop_that_dissolves_a_question_group_reseats_the_survivor_it_pinned() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let float = world.types_mut().float();
    let ints_floats = world.types_mut().union(int, float);
    let key = crate::ground_value::MapKey::Atom("a".to_string());
    let narrow_map = world.types_mut().map(&[(key.clone(), int)]);
    let wide_map = world.types_mut().map(&[(key, ints_floats)]);
    let atom_a = world.types_mut().atom_lit("a");
    let atom_c = world.types_mut().atom_lit("c");
    let atoms_a_c = world.types_mut().union(atom_a, atom_c);
    let two = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "impl_two", 2);
    let zero = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "impl_zero", 2);
    let target = |callee, map, atom| CallTargetSummary {
        callee: SelectedCallee::Function(callee),
        surface_inputs: vec![map, atom],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let narrow = target(two, narrow_map, atom_a);
    let sibling = target(zero, wide_map, atom_a);
    let wide = target(two, wide_map, atoms_a_c);
    let arrival = vec![narrow, sibling.clone(), wide.clone()];

    let observable = observable_inputs(world.types_mut(), &target_surfaces(&arrival));
    let questions = runtime_questions(world.types_mut(), &observable);
    assert_eq!(
        questions[0], questions[1],
        "the dropped arm and the survivor must ask ONE question, or this is not the shape \
             under test",
    );
    assert_ne!(
        questions[1], questions[2],
        "and the arm that stands in for the dropped one must ask another, or there is no \
             group to dissolve",
    );
    assert_eq!(
        specificity_order(world.types(), &questions, &observable),
        vec![2, 0, 1],
        "with all three arms the group {{N, S}} cannot cover W's surface and W covers it, so \
             the seat puts W first and S receives nothing",
    );

    let summary = CallSiteSummary {
        targets: arrival,
        return_ty: None,
    };
    let CallDestinations::Dispatch(dispatch) =
        call_destinations(world.types_mut(), &summary).expect("destinations should compile")
    else {
        panic!("two arms of two callees the atom sets separate are two destinations");
    };
    assert_eq!(
        dispatch.targets,
        vec![sibling, wide],
        "dropping N leaves S judged alone, coverage then runs both ways and precision seats S \
             FIRST -- so a map at `:a` reaches impl_zero, which no arrival of the three arms ever \
             did",
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
///
/// That both SURVIVE is this test's claim. Which is tested first is
/// [`specificity_order`]'s: neither reducer's domain contains the other's,
/// so the canonical tie-break seats them and no value's destination turns
/// on the answer.
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
        extern_params: None,
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

    assert!(
        dispatch.targets.len() == summary.targets.len()
            && summary.targets.iter().all(|target| dispatch.targets.contains(target)),
        "neither arm stands in for the other once the reducer column is a real question: {:#?}",
        dispatch.targets,
    );
    assert!(
        dispatch.plan.graph.nodes.iter().any(|node| matches!(
            node,
            DispatchNode::Test {
                predicate: RegionPredicate {
                    subject: SubjectId(1),
                    ..
                },
                ..
            }
        )),
        "the compiled graph must ask which reducer arrived: {:#?}",
        dispatch.plan.graph.nodes,
    );
}

/// The callable envelope reaches a closure NESTED IN A TUPLE, and it names
/// which callable it is.
///
/// `{:tag, #66}` and `{:tag, #68}` are two questions: a closure value's
/// heap word at `+8` names the code it was minted from, the tuple test
/// reads position 1 with the very same comparison a top-level argument
/// would get, and neither arm can take the other's values.
///
/// This is fz-kdt.119's nested half, and it is gated HERE rather than by a
/// fixture on purpose: a closure nested in a tuple and threaded through a
/// forwarding hop compiles on no path today (fz-kdt.137, pre-existing), so
/// the acceptance program that would exercise it cannot be written yet.
/// When fz-kdt.137 lands, this claim gets a three-door fixture too.
#[test]
fn a_closure_nested_in_a_tuple_is_named_by_the_test() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world
        .types_mut()
        .define_test_callable(ClosureTarget(66), "boxed_one", 1);
    world
        .types_mut()
        .define_test_callable(ClosureTarget(68), "boxed_other", 1);
    let tag = world.types_mut().atom_lit("tag");
    let one = world.types_mut().closure_lit(ClosureTarget(66), Vec::new(), 1);
    let other = world.types_mut().closure_lit(ClosureTarget(68), Vec::new(), 1);
    let boxed_one = world.types_mut().tuple(&[tag, one]);
    let boxed_other = world.types_mut().tuple(&[tag, other]);
    let apply = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "apply_boxed", 1);
    let target = |boxed| CallTargetSummary {
        callee: SelectedCallee::Function(apply),
        surface_inputs: vec![boxed],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };

    let questions = target_questions(world.types_mut(), &[target(boxed_one), target(boxed_other)]);
    assert_ne!(
        questions[0], questions[1],
        "a nested callable position must be a question, or the tuple hides the one thing \
             about a closure the runtime can read",
    );
    assert!(
        !questions[0][0].overlaps(&questions[1][0]),
        "and the two questions must be disjoint: no value passes both",
    );

    let CallDestinations::Dispatch(dispatch) = call_destinations(
        world.types_mut(),
        &CallSiteSummary {
            targets: vec![target(boxed_one), target(boxed_other)],
            return_ty: None,
        },
    )
    .expect("destinations should compile") else {
        panic!("two boxed lambdas the runtime can name are two destinations");
    };
    assert_eq!(dispatch.targets.len(), 2, "neither arm stands in for the other");
}

/// The other half of the same law: the envelope preserves the whole
/// CONSTRUCTION, identity and captures alike.
///
/// A closure's heap word at `+8` is the address of the construction
/// wrapper that minted it, and a wrapper is one function at ONE capture
/// layout -- so one callable closed over an `int` and the same callable
/// closed over a `float` are two words, and the runtime can tell them
/// apart without ever loading a capture. `{:tag, #66(int)}` and
/// `{:tag, #66(float)}` are therefore two questions at every depth,
/// exactly as they are at depth 0 (fz-kdt.127).
#[test]
fn a_nested_callables_captures_are_a_question() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world
        .types_mut()
        .define_test_callable(ClosureTarget(66), "capturing_callable", 1);
    let tag = world.types_mut().atom_lit("tag");
    let int = world.types_mut().int();
    let float = world.types_mut().float();
    let over_int = world.types_mut().closure_lit(ClosureTarget(66), vec![int], 1);
    let over_float = world.types_mut().closure_lit(ClosureTarget(66), vec![float], 1);
    let boxed_int = world.types_mut().tuple(&[tag, over_int]);
    let boxed_float = world.types_mut().tuple(&[tag, over_float]);
    let apply = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "apply_boxed", 1);
    let target = |boxed| CallTargetSummary {
        callee: SelectedCallee::Function(apply),
        surface_inputs: vec![boxed],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };

    assert_ne!(boxed_int, boxed_float, "the lattice keeps the two capture types apart");
    let questions = target_questions(world.types_mut(), &[target(boxed_int), target(boxed_float)]);
    assert_ne!(
        questions[0], questions[1],
        "and so does the runtime: two capture layouts are two construction wrappers, one \
             tuple deep as at the top",
    );
    assert!(
        !questions[0][0].overlaps(&questions[1][0]),
        "and the two questions must be disjoint: no value passes both",
    );

    let CallDestinations::Dispatch(dispatch) = call_destinations(
        world.types_mut(),
        &CallSiteSummary {
            targets: vec![target(boxed_int), target(boxed_float)],
            return_ty: None,
        },
    )
    .expect("destinations should compile") else {
        panic!("two boxed constructions the runtime can name are two destinations");
    };
    assert_eq!(dispatch.targets.len(), 2, "neither arm stands in for the other");
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
    world
        .types_mut()
        .define_test_callable(ClosureTarget(66), "multiply_by_two", 2);
    world
        .types_mut()
        .define_test_callable(ClosureTarget(68), "multiply_by_three", 2);
    let int = world.types_mut().int();
    let one_reducer = world.types_mut().closure_lit(ClosureTarget(66), Vec::new(), 2);
    let other_reducer = world.types_mut().closure_lit(ClosureTarget(68), Vec::new(), 2);
    let apply = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "apply_twice", 2);
    let target = |reducer| CallTargetSummary {
        callee: SelectedCallee::Function(apply),
        surface_inputs: vec![int, reducer],
        activation: None,
        activation_inputs: None,
        extern_params: None,
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
    assert!(
        dispatch.targets.len() == summary.targets.len()
            && summary.targets.iter().all(|target| dispatch.targets.contains(target)),
        "both arms stay, and now each is reachable: {:#?}",
        dispatch.targets,
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
///
/// And precision is worth spending: `:timeout` is tested first, so a
/// `:timeout` runs the body specialized on it rather than the one that
/// takes anything (fz-kdt.129).
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
        extern_params: None,
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
        dispatch.targets,
        vec![target(timeout), target(any)],
        "both arms ask questions the runtime can tell apart, and the narrower one is tested first",
    );
}

/// fz-kdt.129: the arms the runtime CAN separate are seated by what they
/// say, not by when they arrived -- and what they say includes the surface
/// their tests were projected from.
///
/// This is the pair the defect was measured on -- `enum_predicate_search`'s
/// `List.reduce_while_step/3` callsite. Its narrow arm (`{:halt, :false}`
/// reduced by `Enum.empty?/1#lambda`) puts a test to the runtime that its
/// wide one's test (`{:cont, :true} | {:halt, :false}` reduced by any of
/// three lambdas) admits every value of: one 2-tuple test either way, and
/// one lambda out of the three. Both arms are real destinations -- the
/// callable axis tells them apart (fz-kdt.125) -- so neither is dropped and
/// their order was the semantic fixpoint's, which is the agenda's: FIFO
/// seated the wide arm first and LIFO the narrow one, and one lens's
/// artifact stopped being a function of its program.
///
/// The NARROW arm is seated first, and fz-kdt.119 is why the answer moved.
///
/// It used to be the wide arm, and the reasoning was coverage: the two
/// asked one and the same question of the state -- "a 2-tuple" -- so the
/// plan was blind to the difference between `{:halt, :false}` and
/// `{:cont, :true}`, and only the wide arm's surface named both. Seat the
/// narrow arm ahead of it and a `{:cont, :true}` carrying the shared lambda
/// satisfied every question the narrow arm asked and ran a body that never
/// named it, so precision had to yield to coverage.
///
/// The state test is now per position, and both positions are ATOMS. A
/// `{:cont, :true}` fails the narrow arm's first question outright, so
/// there is nothing left for coverage to protect: the pair overlaps
/// NOWHERE erasing, `Covering` holds both ways, and the second conjunct --
/// precision -- settles it for the arm that named its values most tightly.
/// The wide arm still receives everything the narrow one's test refuses.
///
/// Both arrival orders are legal, so both must produce ONE plan.
#[test]
fn distinguishable_arms_are_seated_by_what_they_say_not_by_when_they_arrived() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let list = world.types_mut().list(int);
    let cont_atom = world.types_mut().atom_lit("cont");
    let halt_atom = world.types_mut().atom_lit("halt");
    let true_atom = world.types_mut().atom_lit("true");
    let false_atom = world.types_mut().atom_lit("false");
    let cont_true = world.types_mut().tuple(&[cont_atom, true_atom]);
    let halt_false = world.types_mut().tuple(&[halt_atom, false_atom]);
    let wide_state = world.types_mut().union(cont_true, halt_false);
    let empty = world.types_mut().closure_lit(ClosureTarget(1), Vec::new(), 2);
    let all_one = world.types_mut().closure_lit(ClosureTarget(2), Vec::new(), 2);
    let all_two = world.types_mut().closure_lit(ClosureTarget(3), Vec::new(), 2);
    let some_all = world.types_mut().union(all_one, all_two);
    let wide_reducer = world.types_mut().union(some_all, empty);
    let step = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "reduce_while_step", 3);
    let target = |state, reducer| CallTargetSummary {
        callee: SelectedCallee::Function(step),
        surface_inputs: vec![list, state, reducer],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let narrow = target(halt_false, empty);
    let wide = target(wide_state, wide_reducer);

    for arrival in [vec![wide.clone(), narrow.clone()], vec![narrow.clone(), wide.clone()]] {
        let summary = CallSiteSummary {
            targets: arrival.clone(),
            return_ty: None,
        };
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("two arms the callable axis separates are two destinations");
        };
        assert_eq!(
            dispatch.targets,
            vec![narrow.clone(), wide.clone()],
            "the plan must test the more precise arm first whichever order it arrived in, \
                 and this one arrived {arrival:#?}",
        );
    }
}

/// A narrower TYPE is not a licence to be seated first.
///
/// These three arms are `enum_predicate_search`'s, and they are what
/// refuted ordering on observable surfaces. `list(int)` is a subtype of
/// `list(int | :ok | :true)`, so a surface-ordered seat calls the third arm
/// the narrowest and tests it first -- but every list is one and the same
/// "a non-empty list" to the runtime, and that arm's CALLABLE test admits
/// all three lambdas where its siblings' admit one. Seated first it takes
/// every value the pair was going to receive and hands lists of atoms to a
/// body that reads their heads as ints: `fz_list_head_int_ref` aborts the
/// process on the native and JIT doors, while the interpreter's dynamic
/// tags hide it.
///
/// Coverage keeps it last. Against `list(int | :ok | :true)` it is a
/// strictly narrower surface at a position both read blind, so the mixed
/// arm covers it and is seated first; against `list(:false | :true)` no arm
/// covers the other and arrival order stands. Every seat here is one the
/// arms justify, and the widest CALLABLE test still ends up last.
#[test]
fn an_arm_whose_test_admits_more_is_seated_after_the_arms_it_would_swallow() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok_atom = world.types_mut().atom_lit("ok");
    let true_atom = world.types_mut().atom_lit("true");
    let false_atom = world.types_mut().atom_lit("false");
    let bools = world.types_mut().union(false_atom, true_atom);
    let ints_oks = world.types_mut().union(int, ok_atom);
    let mixed = world.types_mut().union(ints_oks, true_atom);
    let bool_list = world.types_mut().list(bools);
    let mixed_list = world.types_mut().list(mixed);
    let int_list = world.types_mut().list(int);
    let all_one = world.types_mut().closure_lit(ClosureTarget(1), Vec::new(), 2);
    let all_two = world.types_mut().closure_lit(ClosureTarget(2), Vec::new(), 2);
    let empty = world.types_mut().closure_lit(ClosureTarget(3), Vec::new(), 2);
    let two_or_empty = world.types_mut().union(all_two, empty);
    let any_of_three = world.types_mut().union(all_one, two_or_empty);
    let step = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "reduce_while_step", 3);
    let target = |list, reducer| CallTargetSummary {
        callee: SelectedCallee::Function(step),
        surface_inputs: vec![list, int, reducer],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let bools_arm = target(bool_list, all_one);
    let mixed_arm = target(mixed_list, all_one);
    let widest_arm = target(int_list, any_of_three);
    let summary = CallSiteSummary {
        targets: vec![bools_arm.clone(), mixed_arm.clone(), widest_arm.clone()],
        return_ty: None,
    };

    let CallDestinations::Dispatch(dispatch) =
        call_destinations(world.types_mut(), &summary).expect("destinations should compile")
    else {
        panic!("three arms the callable column separates are three destinations");
    };

    assert_eq!(
        dispatch.targets,
        vec![bools_arm, mixed_arm, widest_arm],
        "the arm whose callable test admits all three lambdas must be tested last, however \
             narrow its element type reads",
    );
}

/// fz-kdt.131's law at the shape that refuted seating the narrower TEST
/// first -- and the shape fz-kdt.107 step 3 takes off the table.
///
/// `dispatch_seat_element_blind`'s two arms. The int arm's test used to be
/// strictly INSIDE the atom arm's -- the same "a list" question, the same
/// `:true` question, and a callable set of one against a set of two -- so
/// every containment rule seated it first. Then `Enum.all?([:ok, :ok])`
/// carrying the shared `all?/1` lambda satisfied all three of its
/// questions, because a list test could not see elements, and reached the
/// body that reads heads as ints: `fz_list_head_int_ref` aborted on the
/// JIT and native doors. Coverage was the only thing holding the pair,
/// because neither surface covers the other at the list position.
///
/// The list questions have DISJOINT heads now -- one admits an atom head,
/// the other an int head -- so the only value that passes both is `[]`,
/// which carries nothing for either body to misread, and coverage has
/// nothing left to protect. Both halves are asserted here: the tests no
/// longer meet on an erasing axis, and the seat still leaves the pair as
/// it arrived,
/// because neither test is inside the other and there is nothing to
/// prefer. The fixture that names this shape stops aborting under every
/// arm seed the fz-kdt.141 stress produces.
#[test]
fn arms_over_disjoint_element_types_cannot_take_each_others_values() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok_atom = world.types_mut().atom_lit("ok");
    let true_atom = world.types_mut().atom_lit("true");
    let atom_list = world.types_mut().list(ok_atom);
    let int_list = world.types_mut().list(int);
    let all_one = world.types_mut().closure_lit(ClosureTarget(1), Vec::new(), 2);
    let empty = world.types_mut().closure_lit(ClosureTarget(2), Vec::new(), 2);
    let either = world.types_mut().union(all_one, empty);
    let step = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "reduce_while_step", 3);
    let target = |list, reducer| CallTargetSummary {
        callee: SelectedCallee::Function(step),
        surface_inputs: vec![list, true_atom, reducer],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let atoms_arm = target(atom_list, either);
    let ints_arm = target(int_list, all_one);

    let questions = target_questions(world.types_mut(), &[atoms_arm.clone(), ints_arm.clone()]);
    assert!(
        !questions[0][0].overlaps_on_an_erasing_axis(&questions[1][0]),
        "a list of atoms and a list of ints ask disjoint heads, so the only value that passes \
             both is `[]` -- one value carrying nothing either body can misread",
    );

    for order in [[&atoms_arm, &ints_arm], [&ints_arm, &atoms_arm]] {
        let arrival = order.into_iter().cloned().collect::<Vec<_>>();
        let summary = CallSiteSummary {
            targets: arrival.clone(),
            return_ty: None,
        };
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("two arms the callable axis separates are two destinations");
        };
        assert_eq!(
            dispatch.targets, arrival,
            "neither test is inside the other, so the seat has nothing to prefer and arrival \
                 stands -- harmlessly now, because the two questions are disjoint",
        );
    }
}

/// THE PRECONDITION MAY NOT OVER-SEPARATE: wherever two surfaces share a
/// value, the tests they project to must admit one.
///
/// This is the soundness half of fz-kdt.186. Calling a pair `Separated`
/// buys the seat the right to leave it alone AND buys the drop the right
/// to remove one of its arms, so a projection that reported "disjoint"
/// about two surfaces a value actually lies in both of would be a routing
/// decision made on a fiction -- the same shape of error, in the other
/// direction.
///
/// The implication holds by construction: a test ADMITS everything its
/// surface holds (it is a coarsening), so a value in both surfaces passes
/// both tests. This gate holds every axis to it over a battery whose pairs
/// exercise each way the projection can lose precision -- `any` against
/// every kind, an inexact tuple against an exact one, a cofinite atom set,
/// a list that admits `[]` beside one that cannot, callable captures wide
/// and narrow, and the same shapes one level down inside a tuple.
#[test]
fn a_separated_pair_of_tests_is_a_disjoint_pair_of_surfaces() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let t = world.types_mut();
    let any = t.any();
    let int = t.int();
    let float = t.float();
    let ok = t.atom_lit("ok");
    let tail = t.atom_lit("tail");
    let nil = t.atom_lit("nil");
    let int_or_tail = t.union(int, tail);
    let ok_or_tail = t.union(ok, tail);
    let empty = t.empty_list();
    let int_list = t.list(int);
    let tail_list = t.list(tail);
    let any_list = t.list(any);
    let mixed_list = t.list(int_or_tail);
    let ok_tail_list = t.list(ok_or_tail);
    let int_list_or_empty = t.union(int_list, empty);
    let any_pair = t.tuple(&[any, any]);
    let int_pair = t.tuple(&[int, int]);
    let cont_pair = t.tuple(&[ok, int_list]);
    let halt_pair = t.tuple(&[tail, mixed_list]);
    let listy_pair = t.tuple(&[int_list, ok]);
    let listy_pair_wide = t.tuple(&[mixed_list, ok_or_tail]);
    let triple = t.tuple(&[int, int, int]);
    let lam_any = t.closure_lit(ClosureTarget(7), vec![any], 1);
    let lam_int = t.closure_lit(ClosureTarget(7), vec![int], 1);
    let lam_float = t.closure_lit(ClosureTarget(7), vec![float], 1);
    let lam_list = t.closure_lit(ClosureTarget(7), vec![int_list], 1);
    let lam_mixed = t.closure_lit(ClosureTarget(7), vec![mixed_list], 1);
    let other_lam = t.closure_lit(ClosureTarget(8), vec![int], 1);
    let lam_either = t.union(lam_int, other_lam);
    let map_one = t.map(&[]);
    let brand_x = t.mint_brand(int, "X");
    let brand_y = t.mint_brand(int, "Y");
    let not_ok = t.difference(any, ok);
    let not_int = t.difference(any, int);
    let not_lam_int = t.difference(any, lam_int);
    let battery = [
        any,
        int,
        float,
        ok,
        tail,
        nil,
        int_or_tail,
        empty,
        int_list,
        tail_list,
        any_list,
        mixed_list,
        ok_tail_list,
        int_list_or_empty,
        any_pair,
        int_pair,
        cont_pair,
        halt_pair,
        listy_pair,
        listy_pair_wide,
        triple,
        lam_any,
        lam_int,
        lam_float,
        lam_list,
        lam_mixed,
        other_lam,
        lam_either,
        map_one,
        brand_x,
        brand_y,
        not_ok,
        not_int,
        not_lam_int,
    ];

    let mut over_separated = Vec::new();
    let mut shared = 0;
    for left in battery {
        for right in battery {
            let both = world.types_mut().intersect(left, right);
            if world.types().is_empty(&both) {
                continue;
            }
            shared += 1;
            let types = world.types();
            if !types
                .runtime_type_predicate(&left)
                .overlaps(&types.runtime_type_predicate(&right))
            {
                over_separated.push(format!(
                    "{} and {} share {} and their tests claim to be disjoint",
                    types.display(&left),
                    types.display(&right),
                    types.display(&both),
                ));
            }
        }
    }
    assert!(
        over_separated.is_empty(),
        "a test that admits everything its surface holds cannot refuse a value both surfaces hold, \
             and a seat that believed otherwise would leave a reachable pair unseated and drop a live \
             arm: {over_separated:#?}",
    );
    assert!(
        shared > 100,
        "the battery must actually meet: {shared} pairs shared a value",
    );
    let asymmetric = {
        let types = world.types();
        let mut asymmetric = Vec::new();
        for left in battery {
            for right in battery {
                let (a, b) = (
                    types.runtime_type_predicate(&left),
                    types.runtime_type_predicate(&right),
                );
                if a.overlaps(&b) != b.overlaps(&a) {
                    asymmetric.push(format!("{} and {}", types.display(&left), types.display(&right)));
                }
            }
        }
        asymmetric
    };
    assert!(
        asymmetric.is_empty(),
        "\"one value passes both tests\" names no direction, and `Seating::Separated` is read in \
             one direction only -- by `canonically_order_separated_neighbours`, of the pair it is \
             about to swap. An asymmetric reading would make that swap depend on which of the two \
             the caller passed first: {asymmetric:#?}",
    );
    let types = world.types();
    let self_blind = battery
        .into_iter()
        .filter(|ty| !types.is_empty(ty))
        .filter(|ty| {
            let test = types.runtime_type_predicate(ty);
            !test.overlaps(&test)
        })
        .map(|ty| types.display(&ty))
        .collect::<Vec<_>>();
    assert!(
        self_blind.is_empty(),
        "every shape here must project to a test that admits SOMETHING -- a test blind to its own \
             surface is the projection failing to coarsen it, and the implication above would hold of \
             such a pair for no reason at all. `an_untested_position_is_not_a_separation` carries the \
             one shape that does fail it, and keeps it out of the seat: {self_blind:#?}",
    );
}

/// fz-kdt.186: a pair the plan's own tests keep apart OUTRIGHT is not a
/// seat question, however blind some other subject happens to be.
///
/// These are a construction wrapper of `00277_enum_tier0_fixture`, arm 4
/// against arm 9, written down as a two-subject callsite. (It was `w13` in
/// the PUBLISHED numbering of the tree it was measured in; 00277 publishes
/// five wrappers at head, all single-member with no selection plan since
/// fz-kdt.199, so `w13` names nothing in either numbering now -- and a
/// wrapper's published number is not the number a dump prints either, which
/// is fz-kdt.193's.) The shape is what matters and it is written out here:
///
/// ```text
///     arm 4    s0 = :tail    s1 = [:tail]
///     arm 9    s0 = int      s1 = [int] | [int | :tail]
/// ```
///
/// Subject 0 asks an ATOM against an INT, which no value answers both
/// ways, so the plan's own first test routes every value to one arm or the
/// other and the order between them decides nothing. Subject 1 is the list
/// behind it, where the two heads overlap and neither surface contains the
/// other, so the coverage check judged the pair blind there -- and, reading
/// each subject under an `all`, took subject 0's disjointness for
/// "separation" and reported a routing that cannot happen.
///
/// The reading it produced was "arm 9 covers arm 4, seated second", one of
/// the twenty-eight such readings the static census carried on this
/// fixture's seven eleven-member wrappers. There is no value to route, so
/// there is nothing to seat: the pair is `Seating::Separated`,
/// [`seats_before`] is false in both directions, and both arrivals come
/// out as they went in.
#[test]
fn arms_no_value_can_reach_both_of_are_not_a_seat_question() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let tail_atom = world.types_mut().atom_lit("tail");
    let tail_list = world.types_mut().list(tail_atom);
    let int_list = world.types_mut().list(int);
    let int_or_tail = world.types_mut().union(int, tail_atom);
    let mixed_list = world.types_mut().list(int_or_tail);
    let either_list = world.types_mut().union(int_list, mixed_list);
    let member = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "reduce_while_step", 2);
    let target = |head, list| CallTargetSummary {
        callee: SelectedCallee::Function(member),
        surface_inputs: vec![head, list],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let tails_arm = target(tail_atom, tail_list);
    let ints_arm = target(int, either_list);

    let arms = [tails_arm.clone(), ints_arm.clone()];
    let observable = observable_inputs(world.types_mut(), &target_surfaces(&arms));
    let questions = runtime_questions(world.types_mut(), &observable);
    assert!(
        !questions[0][0].overlaps(&questions[1][0]),
        "subject 0 asks `:tail` against `int`, and no value answers both",
    );
    assert!(
        questions[0][1].overlaps_on_an_erasing_axis(&questions[1][1]),
        "subject 1 is the list behind it, where both heads admit `:tail` and neither test reads the \
             tail -- the subject the old reading called blind",
    );
    let types = world.types();
    assert_eq!(
        seating(types, &questions, &observable, &[0], &[1]),
        Seating::Separated,
        "one disjoint subject separates the whole pair: a row is a conjunction over its subjects",
    );
    assert_eq!(
        seating(types, &questions, &observable, &[1], &[0]),
        Seating::Separated,
        "separation is symmetric, so neither direction is a covering one",
    );
    assert!(
        !seats_before(types, &questions, &observable, &[0], &[1])
            && !seats_before(types, &questions, &observable, &[1], &[0]),
        "the seat has no opinion about a pair that routes nothing, in either direction",
    );

    // Read the expected order off the quantity PRODUCTION keys the repair
    // on -- the observable envelope, not the surface it was projected
    // from. The two agree on this pair, which carries no callable, and a
    // gate that mirrored production with the other quantity would stop
    // agreeing on one that did.
    let canonical = match types.cmp_activation_tys(&observable[0], &observable[1]) {
        Ordering::Greater => vec![ints_arm.clone(), tails_arm.clone()],
        _ => vec![tails_arm.clone(), ints_arm.clone()],
    };
    for arrival in [[&tails_arm, &ints_arm], [&ints_arm, &tails_arm]] {
        let targets = arrival.into_iter().cloned().collect::<Vec<_>>();
        let summary = CallSiteSummary {
            targets: targets.clone(),
            return_ty: None,
        };
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("two arms subject 0 separates are two destinations");
        };
        assert_eq!(
            dispatch.targets, canonical,
            "no value reaches both arms, so which of them the fixpoint delivered first is not a \
                 fact about the program: BOTH arrivals come out in one typed activation order, and neither \
                 arm is dropped for the other (fz-kdt.194)",
        );
    }
}

/// THE TRANSITIVITY TRAP, and the honest limit it draws.
///
/// `Separated` is symmetric but NOT transitive: `A|B` separated and `B|C`
/// separated says nothing at all about `A|C`. Three list arms are the
/// smallest witness --
///
/// ```text
///     A  {:p, [int | :ok]}    B  {:q, [int]}    C  {:p, [int | :tail]}
/// ```
///
/// -- where `A|B` and `B|C` are separated at the TAG, which no value
/// answers both ways, while `A|C` carry the same tag and ask the list
/// behind it a question that shares `int` with neither surface containing
/// the other, so they are fz-kdt.131's class and no rule here may decide
/// them. (Two bare lists would not do it: every list type admits `[]`, so
/// even disjoint heads leave a list pair reachable.)
///
/// So there is no run to sort, and the canonical repair does not pretend
/// there is: it swaps ADJACENT separated pairs and stops at `A|C`. What it
/// buys on such a triple is therefore partial, and this gate writes down
/// exactly which part:
///
/// - the repair NEVER moves `A` past `C`. Whichever of them arrived first
///   is still first, at both arrivals, which is the whole safety claim.
/// - the two arrivals below still come out DIFFERENT, because the pair
///   that blocks is the one whose order means something. Where a run is
///   pairwise separated all the way through, the repair does reach one
///   order from every arrival -- `arms_no_value_can_reach_both_of_are_not_a_seat_question`
///   is that case, and it is the one the corpus's 22 artifact movers were.
///
/// A comparison sort would "fix" this by moving `A` past `C` on the
/// strength of a comparator that never asked whether it may. That is the
/// bug this shape exists to forbid.
#[test]
fn a_separated_run_a_meaning_bearing_pair_blocks_is_not_sorted_through() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok = world.types_mut().atom_lit("ok");
    let tail = world.types_mut().atom_lit("tail");
    let p = world.types_mut().atom_lit("p");
    let q = world.types_mut().atom_lit("q");
    let int_or_ok = world.types_mut().union(int, ok);
    let int_or_tail = world.types_mut().union(int, tail);
    let ok_list = world.types_mut().list(int_or_ok);
    let int_list = world.types_mut().list(int);
    let tail_list = world.types_mut().list(int_or_tail);
    let a = world.types_mut().tuple(&[p, ok_list]);
    let b = world.types_mut().tuple(&[q, int_list]);
    let c = world.types_mut().tuple(&[p, tail_list]);
    let callee = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "step", 1);
    let target = |tagged| CallTargetSummary {
        callee: SelectedCallee::Function(callee),
        surface_inputs: vec![tagged],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let (arm_a, arm_b, arm_c) = (target(a), target(b), target(c));
    let arms = [arm_a.clone(), arm_b.clone(), arm_c.clone()];
    {
        let questions = target_questions(world.types_mut(), &arms);
        let observable = observable_inputs(world.types_mut(), &target_surfaces(&arms));
        let types = world.types();
        for (x, y) in [(0, 1), (1, 2)] {
            assert_eq!(
                seating(types, &questions, &observable, &[x], &[y]),
                Seating::Separated,
                "arm {x} and arm {y} ask disjoint TAGS, so no value reaches both",
            );
        }
        assert_eq!(
            seating(types, &questions, &observable, &[0], &[2]),
            Seating::Escaping,
            "the two ends carry one tag and share `int` behind it, and neither surface names \
                 everything the other holds -- separation is not transitive, and this is the pair \
                 that proves it",
        );
    }

    let seated = |world: &mut World, arrival: &[CallTargetSummary]| {
        let summary = CallSiteSummary {
            targets: arrival.to_vec(),
            return_ty: None,
        };
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("three arms the tag question tells apart are three destinations");
        };
        dispatch.targets
    };
    let forwards = seated(&mut world, &[arm_a.clone(), arm_b.clone(), arm_c.clone()]);
    let backwards = seated(&mut world, &[arm_c.clone(), arm_b, arm_a.clone()]);

    let position = |order: &[CallTargetSummary], arm: &CallTargetSummary| {
        order
            .iter()
            .position(|target| target == arm)
            .expect("every arm survives")
    };
    assert!(
        position(&forwards, &arm_a) < position(&forwards, &arm_c),
        "arriving A-before-C, A stays before C: the repair may not decide fz-kdt.131's pair",
    );
    assert!(
        position(&backwards, &arm_c) < position(&backwards, &arm_a),
        "arriving C-before-A, C stays before A -- the same refusal, read the other way",
    );
    assert_ne!(
        forwards, backwards,
        "and so the two arrivals do NOT converge: where a meaning-bearing pair blocks the run, \
             the order is still a function of the arrival, and that residue belongs to fz-kdt.131 \
             rather than to any canonical order",
    );
}

/// The tie the canonical repair can never be handed: two DISTINCT question
/// groups whose keys compare `Equal`.
///
/// The typed activation relation is `Equal` only on identical `Ty` slices, and a group's key is
/// one of its members' observable surfaces. So a tie would mean one surface
/// sitting in two groups -- but the question is a function of the surface,
/// and one question is one group. The repair therefore never has to fall
/// through to a second key, and never has to break a tie by arrival.
///
/// Held on the shape that would produce one if anything did: two arms on
/// two DIFFERENT callees carrying the very same surface.
#[test]
fn two_arms_that_say_the_same_thing_are_one_group_and_never_a_tie() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok = world.types_mut().atom_lit("ok");
    let int_or_ok = world.types_mut().union(int, ok);
    let shared = world.types_mut().list(int_or_ok);
    let separate = world.types_mut().list(ok);
    let left_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "left_impl", 1);
    let right_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "right_impl", 1);
    let target = |function, surface| CallTargetSummary {
        callee: SelectedCallee::Function(function),
        surface_inputs: vec![surface],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let arms = [
        target(left_fn, shared),
        target(right_fn, shared),
        target(left_fn, separate),
    ];
    let observable = observable_inputs(world.types_mut(), &target_surfaces(&arms));
    let questions = runtime_questions(world.types_mut(), &observable);
    let groups = grouped_by_question(&questions);
    assert_eq!(
        groups,
        vec![vec![0, 1], vec![2]],
        "two arms carrying one surface ask one question, so they are ONE group however many \
             callees they name",
    );
    let types = world.types();
    let keys = groups
        .iter()
        .map(|group| canonical_key(types, &observable, group))
        .collect::<Vec<_>>();
    for (x, group_x) in groups.iter().enumerate() {
        for (y, group_y) in groups.iter().enumerate().skip(x + 1) {
            assert_ne!(
                types.cmp_activation_tys(&observable[keys[x]], &observable[keys[y]]),
                Ordering::Equal,
                "distinct groups may never tie under the repair's key -- an equal key is an equal \
                     surface, an equal surface is an equal question, and one question is one group: \
                     {group_x:?} against {group_y:?}",
            );
        }
    }
}

/// A position the plan does NOT test may not separate a pair, and the
/// separation check has to say so itself rather than trust that every
/// realizable test overlaps itself.
///
/// [`dispatch_columns`] drops a position where every arm carries the
/// SAME observable surface -- the plan emits no test there at all -- so a
/// pair "separated" there is separated by nothing the runtime asks. The
/// projection makes that reachable: a tuple clause with a SUBTRACTED
/// signature loses its whole arity in
/// `runtime_type_predicate_tuple_arities`, so `{any, any} & not({int,
/// int})` holds every pair that is not two ints and yet projects to a test
/// admitting nothing, which does not overlap itself.
///
/// Both arms below carry that surface at subject 1 and differ only at
/// subject 0, where `:ok` sits inside `:ok | :tail` on the ATOM axis --
/// separating, so coverage runs both ways and the precision preference
/// seats the narrow arm first. Read subject 1 through `overlaps` alone and
/// the pair is `Separated`, `seats_before(N, W)` is false, and the drop
/// takes the narrow arm for its stand-in: the callsite collapses to
/// `Direct(W)` and `(:ok, pair)` runs a body no arrival of these two arms
/// ever sent it to. That is the relative-soundness theorem
/// [`unroutable_alternatives`] rests on, broken by a question the plan
/// never puts.
///
/// One and the same question separates nothing, so [`seating`] skips a
/// position the two arms ask identically, and the narrow arm survives.
#[test]
fn an_untested_position_is_not_a_separation() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let callee = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "impl", 2);
    let (ok, ok_or_tail, carved) = {
        let types = world.types_mut();
        let any = types.any();
        let int = types.int();
        let ok = types.atom_lit("ok");
        let tail = types.atom_lit("tail");
        let ok_or_tail = types.union(ok, tail);
        let any_pair = types.tuple(&[any, any]);
        let int_pair = types.tuple(&[int, int]);
        let carved = types.difference(any_pair, int_pair);
        (ok, ok_or_tail, carved)
    };
    assert!(
        !world.types().is_empty(&carved),
        "the shared surface must be REALIZABLE, or the arms would be dead for an honest reason",
    );
    let target = |head, second| CallTargetSummary {
        callee: SelectedCallee::Function(callee),
        surface_inputs: vec![head, second],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let narrow = target(ok, carved);
    let wide = target(ok_or_tail, carved);
    let arms = [narrow.clone(), wide.clone()];
    let observable = observable_inputs(world.types_mut(), &target_surfaces(&arms));
    let questions = runtime_questions(world.types_mut(), &observable);
    assert_eq!(
        dispatch_columns(2, &observable, &questions),
        vec![0],
        "subject 1 is the same surface on both arms, so the plan tests subject 0 and nothing else",
    );
    assert!(
        !questions[0][1].overlaps(&questions[1][1]),
        "the shared surface's own test does not overlap ITSELF -- the projection defect this gate \
             refuses to let decide a routing",
    );
    let types = world.types();
    assert_eq!(
        seating(types, &questions, &observable, &[0], &[1]),
        Seating::Covering,
        "a question both arms ask identically separates nothing, whatever that question admits",
    );
    assert!(
        seats_before(types, &questions, &observable, &[0], &[1]),
        "subject 0 is an ATOM pair, which separates, so coverage runs both ways and precision seats \
             the arm that named its values most tightly",
    );
    assert!(
        stands_in_for(types, &same_callee(&arms), &observable, &questions, 1, 0),
        "the wide arm is the narrow one's stand-in, which is what puts the drop in reach at all",
    );
    assert!(
        unroutable_alternatives(types, &same_callee(&arms), &observable, &questions).is_empty(),
        "the seat puts the narrow arm FIRST, so the drop may not take it: dropping it would send \
             `(:ok, pair)` to the wide body, which no arrival of these two arms does",
    );
    let summary = CallSiteSummary {
        targets: arms.to_vec(),
        return_ty: None,
    };
    let CallDestinations::Dispatch(dispatch) =
        call_destinations(world.types_mut(), &summary).expect("destinations should compile")
    else {
        panic!("both arms survive, so the callsite is a dispatch and not a direct call");
    };
    assert_eq!(
        dispatch.targets,
        vec![narrow, wide],
        "both arms are destinations and the narrow one is tested first",
    );
}

/// fz-kdt.107 step 3's trio, every arrival order: the covered arm is no
/// destination, and the pair no seat can decide arrives as it arrives.
///
/// These are `enum_predicate_search`'s three `List.reduce_while_cont/3`
/// arms, and they are the population whose native abort named fz-kdt.107:
///
/// ```text
///     A   [:false | :true]
///     B   [int | :ok | :true]
///     C   [int]
/// ```
///
/// Before the head question all three were "a non-empty list", one group,
/// arrival-decided -- and a legal arrival that put C first handed
/// `[:false, :true]` to a body reading heads as ints
/// (`fz_list_head_int_ref`, exit 134 on both compiled doors).
///
/// B AND C OVERLAP AT THE HEAD (both admit an int) and differ only in a
/// tail no test reads, so that pair is erasing and no seat that puts C
/// first is escape-free. B is the same callee on a strictly wider surface
/// whose test admits every value C's admits, so B stands in for C and the
/// seat would never put C ahead of it: C is dropped, and the values it
/// would have taken reach B, whose surface names them. A against C is
/// DISJOINT heads, a real separation, so A is no stand-in for C and
/// dropping C loses A nothing. A against B overlaps at `:true` and neither
/// surface contains the other: no seat is escape-free, neither stands in
/// for the other, and arrival stands.
///
/// So on all six arrivals the answer is the same two arms in the order
/// they arrived in. What the trio used to pin -- that on the ONE arrival
/// `[C, A, B]` the insertion pass could not carry B past the A/B pair it
/// may not decide, leaving C ahead of B and `[1, :ok]` reaching the
/// int-reading body -- is the seat this ticket removes by removing C.
///
/// The A/B pair is PINNED, not fixed. It is fz-kdt.131's facet 3 --
/// overlap without containment -- whose cure is a repr-level or
/// minting-level decision, not a seat and not a drop.
#[test]
fn a_list_head_drops_the_covered_arm_and_leaves_the_inseparable_pair_as_it_arrived() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok_atom = world.types_mut().atom_lit("ok");
    let true_atom = world.types_mut().atom_lit("true");
    let false_atom = world.types_mut().atom_lit("false");
    let bools = world.types_mut().union(false_atom, true_atom);
    let ints_oks = world.types_mut().union(int, ok_atom);
    let mixed = world.types_mut().union(ints_oks, true_atom);
    let bool_list = world.types_mut().list(bools);
    let mixed_list = world.types_mut().list(mixed);
    let int_list = world.types_mut().list(int);
    let reducer = world.types_mut().closure_lit(ClosureTarget(1), Vec::new(), 2);
    let step = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "reduce_while_cont", 3);
    let target = |list| CallTargetSummary {
        callee: SelectedCallee::Function(step),
        surface_inputs: vec![list, true_atom, reducer],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let arms = [target(bool_list), target(mixed_list), target(int_list)];
    let name = |target: &CallTargetSummary| {
        if target.surface_inputs[0] == bool_list {
            "A"
        } else if target.surface_inputs[0] == mixed_list {
            "B"
        } else {
            "C"
        }
    };

    let arrivals = [
        ["A", "B", "C"],
        ["A", "C", "B"],
        ["B", "A", "C"],
        ["B", "C", "A"],
        ["C", "A", "B"],
        ["C", "B", "A"],
    ];
    let slot = |which: &str| match which {
        "A" => 0,
        "B" => 1,
        _ => 2,
    };
    for arrived in arrivals {
        let summary = CallSiteSummary {
            targets: arrived.iter().map(|which| arms[slot(which)].clone()).collect(),
            return_ty: None,
        };
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("A and B are two destinations no rule may collapse, arrived {arrived:?}");
        };
        let seated = dispatch.targets.iter().map(name).collect::<Vec<_>>();
        let wanted = arrived
            .iter()
            .copied()
            .filter(|which| *which != "C")
            .collect::<Vec<_>>();
        assert_eq!(
            seated, wanted,
            "B stands in for C on every arrival, so C is no destination on any of them, and \
                 the A/B pair no seat can decide keeps the order it arrived in -- arrived \
                 {arrived:?}",
        );
    }
}

/// The tail the head test cannot see, and the arm it leaves nothing for.
///
/// Two arms of ONE function, `[int]` and `[int | :ok]`, identical
/// everywhere else. Their head questions OVERLAP -- both admit an int --
/// and where they differ is the TAIL, which no test reads. So this pair is
/// erasing however precisely the heads themselves are decided, and the
/// only escape-free seat is the covering one: `[int | :ok]` first.
///
/// THIS IS THE GATE THAT WOULD HAVE CAUGHT THE REFUTED SEAT. Reading "the
/// heads differ" as separation makes this pair separating, and the
/// precision preference then seats the strictly-narrower `[int]` test
/// first -- at which point `[1, :ok]` passes its head question and lands in
/// the body that reads every element as an int. That is the abort the list
/// axis exists to kill, re-created by the axis meant to kill it.
///
/// And a seat the pass will never take is no destination. `[int | :ok]`
/// stands in for `[int]` -- one callee, a strictly wider surface, a test
/// that admits every value the narrow one's admits -- and `seats_before`
/// refuses to put `[int]` ahead of it, so the drop takes the narrow arm
/// and the callsite is a `Direct` call on the wide one. Every value the
/// narrow arm could have received passes the wide arm's test and lands in
/// a body whose surface names it, which is what the arrival that seats the
/// wide arm first already did.
#[test]
fn an_arm_whose_head_overlaps_a_wider_one_is_no_destination_beside_it() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok_atom = world.types_mut().atom_lit("ok");
    let true_atom = world.types_mut().atom_lit("true");
    let ints_oks = world.types_mut().union(int, ok_atom);
    let int_list = world.types_mut().list(int);
    let int_ok_list = world.types_mut().list(ints_oks);
    let reducer = world.types_mut().closure_lit(ClosureTarget(1), Vec::new(), 2);
    let step = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "reduce_while_step", 3);
    let target = |list| CallTargetSummary {
        callee: SelectedCallee::Function(step),
        surface_inputs: vec![list, true_atom, reducer],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let narrow = target(int_list);
    let wide = target(int_ok_list);

    for order in [[&narrow, &wide], [&wide, &narrow]] {
        let arrival = order.into_iter().cloned().collect::<Vec<_>>();
        let summary = CallSiteSummary {
            targets: arrival.clone(),
            return_ty: None,
        };
        let destinations = call_destinations(world.types_mut(), &summary).expect("destinations should compile");
        assert_eq!(
            destinations,
            CallDestinations::Direct(wide.clone()),
            "[int] and [int | :ok] agree at the head and disagree only in a tail no test \
                 reads, so the narrow arm can never be seated first and is no destination at all \
                 -- arrived {arrival:?}",
        );
    }
}

/// The carve-out fz-kdt.107 refuted a canonical order without: arms one
/// runtime question cannot separate keep the order they arrived in.
///
/// Two DIFFERENT functions taking a MAP with the same keys at different
/// value types. A map test is a KIND check -- the axis is `Erasing`
/// because a map value tells the runtime it is a map and nothing about
/// what it holds -- so `%{a: int}` and `%{a: float}` are one and the same
/// question. Nothing the plan emits tells the arms apart, and whichever is
/// listed first receives every value the pair can see. Re-deciding that is
/// not a reordering, it is a rerouting -- fz-kdt.107 prototyped a
/// canonical order over this class and got `{:done, 3}` where
/// `{:halted, 3}` was due -- so the order is keyed on the GROUP: a key
/// constant across a group cannot move a member of one.
///
/// THE SHAPE HAS MOVED THREE TIMES, and each move is a population leaving
/// this carve-out for a real question. It was two tagged tuples until
/// fz-kdt.119 gave tuples a per-position test, which separates tags. It
/// was `list(int)` against `list(:ok)` until fz-kdt.107 step 3 gave the
/// list axis a head question, which separates disjoint element types. It
/// was one lambda at two capture types until fz-kdt.127 made the callable
/// axis name the CONSTRUCTION, which separates capture layouts. What is
/// left is the contents of the kinds whose test is a kind check: a map, a
/// binary, a resource, an unnamed struct.
#[test]
fn runtime_indistinguishable_arms_keep_the_order_they_arrived_in() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let float = world.types_mut().float();
    let key = crate::ground_value::MapKey::Atom("a".to_string());
    let over_int = world.types_mut().map(&[(key.clone(), int)]);
    let over_float = world.types_mut().map(&[(key, float)]);
    let first_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "int_impl", 1);
    let second_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "float_impl", 1);
    let target = |function, reducer| CallTargetSummary {
        callee: SelectedCallee::Function(function),
        surface_inputs: vec![reducer],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let ints = target(first_fn, over_int);
    let atoms = target(second_fn, over_float);

    assert_ne!(over_int, over_float, "the lattice keeps the two value types apart");

    let questions = target_questions(world.types_mut(), &[ints.clone(), atoms.clone()]);
    assert_eq!(
        questions[0], questions[1],
        "the two arms must put one and the same question, or this gate is not about the \
             inseparable class at all",
    );

    for order in [[&ints, &atoms], [&atoms, &ints]] {
        let arrival = order.into_iter().cloned().collect::<Vec<_>>();
        let summary = CallSiteSummary {
            targets: arrival.clone(),
            return_ty: None,
        };
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("two functions are two destinations, however alike their domains look");
        };
        assert_eq!(
            dispatch.targets, arrival,
            "no canonical order may move an arm the runtime cannot tell from its neighbour",
        );
    }
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
                extern_params: None,
                return_ty: None,
            },
            CallTargetSummary {
                callee: SelectedCallee::Function(function),
                surface_inputs: vec![int, halt],
                activation: None,
                activation_inputs: None,
                extern_params: None,
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
            .graph
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
        boundary_input_demands: Box::new([]),
    };

    let edges = [edge(atom), edge(tuple)];
    let dispatch = construction_member_selection(world.types_mut(), &edges)
        .expect("callable flow dispatch should compile")
        .plan
        .expect("distinct callable members require dispatch");

    assert!(
        dispatch
            .graph
            .subjects
            .iter()
            .any(|subject| subject.source == SubjectSource::Input { ordinal: 1 }),
        "the bridge must discriminate its state argument, not its shared entry argument"
    );
}

/// A construction wrapper's own edge builder, so the fz-kdt.179 probes can
/// say what a member's surface is and nothing else.
fn wrapper_edge(world: &mut World, surface: Vec<Ty>) -> CallableFlowEdge {
    let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "wrapped", surface.len());
    let activation = super::super::identity::ActivationKey::from_inputs(
        crate::compiler2::RootId::for_test(0),
        function,
        &surface,
        world.types_mut(),
    );
    CallableFlowEdge {
        surface: super::super::semantic::CallableSurface {
            inputs: surface.clone(),
        },
        resolution: super::super::identity::ExecutableKey {
            activation,
            need: crate::compiler2::ExecutableNeed::Value,
        },
        capture_semantic_inputs: Box::default(),
        surface_semantic_inputs: (0..surface.len()).collect(),
        boundary_input_demands: Box::new([]),
    }
}

/// fz-kdt.179 attack 1: a member whose sibling stands in for it completely
/// is not a destination, and what is left is the sibling ALONE -- so the
/// wrapper calls it directly instead of testing for it.
#[test]
fn a_wrapper_member_its_sibling_stands_in_for_is_not_a_destination() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let tail = world.types_mut().atom_lit("tail");
    let int_or_tail = world.types_mut().union(int, tail);
    let narrow = world.types_mut().list(int);
    let wide = world.types_mut().list(int_or_tail);
    let edges = [
        wrapper_edge(&mut world, vec![narrow]),
        wrapper_edge(&mut world, vec![wide]),
    ];

    let selection = construction_member_selection(world.types_mut(), &edges).expect("selection should compile");
    assert_eq!(
        selection.members,
        vec![1],
        "`[int]` passes `[int | :tail]`'s head test and its body names less, so it is the arm the seat              would never put first and the drop takes it",
    );
    assert!(
        selection.plan.is_none(),
        "one member left is one destination, and a wrapper with one destination calls it",
    );
}

/// fz-kdt.179 attack 2: two members that overlap without either surface
/// containing the other are fz-kdt.131's residue, and member selection
/// inherits it exactly as a callsite does -- no drop, no seat, arrival
/// order kept.
#[test]
fn wrapper_members_that_overlap_without_containment_keep_arrival_order() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok = world.types_mut().atom_lit("ok");
    let tail = world.types_mut().atom_lit("tail");
    let left = world.types_mut().union(int, ok);
    let right = world.types_mut().union(int, tail);
    let left_list = world.types_mut().list(left);
    let right_list = world.types_mut().list(right);
    let edges = [
        wrapper_edge(&mut world, vec![left_list]),
        wrapper_edge(&mut world, vec![right_list]),
    ];

    let selection = construction_member_selection(world.types_mut(), &edges).expect("selection should compile");
    assert_eq!(
        selection.members,
        vec![0, 1],
        "neither surface contains the other, so no member stands in for its sibling and no seat between              them is safer than the one they arrived in (fz-kdt.131)",
    );
}

/// fz-kdt.179 attack 3: the weld is re-derived, not assumed. Row `i` names
/// member `i` of the list transport builds FROM `members`, whatever the
/// edge list's own order was.
#[test]
fn a_seated_selection_welds_row_index_to_member_index() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok = world.types_mut().atom_lit("ok");
    let tail = world.types_mut().atom_lit("tail");
    let left = world.types_mut().union(int, ok);
    let right = world.types_mut().union(int, tail);
    let left_list = world.types_mut().list(left);
    let right_list = world.types_mut().list(right);
    let edges = [
        wrapper_edge(&mut world, vec![left_list]),
        wrapper_edge(&mut world, vec![right_list]),
    ];

    let selection = construction_member_selection(world.types_mut(), &edges).expect("selection should compile");
    let plan = selection
        .plan
        .expect("two members the runtime can tell apart need a plan");
    assert_eq!(
        plan.outcomes
            .iter()
            .map(|outcome| outcome.body_id as usize)
            .collect::<Vec<_>>(),
        (0..selection.members.len()).collect::<Vec<_>>(),
        "a selection row's `body_id` is its index in the seated member list, which is the list              transport builds -- the fz-kdt.108 weld, re-derived from the seat",
    );
}

/// fz-kdt.179 REVIEW PROBE (attack 5): the case the corpus does not
/// exercise -- a wrapper whose members the seat must REORDER, not merely
/// drop. `[:ok, carved]` sits inside `[:ok | :tail, carved]` on the atom
/// axis at subject 0, which SEPARATES, so coverage runs both ways and the
/// precision preference seats the narrow member first; because the seat
/// puts it first, the drop may NOT take it (both survive). This is the
/// reorder path, and the point of the probe is that the weld still holds:
/// `members` is the SEATED order (narrow first), whatever the edge list's
/// own typed activation order was, and each row's `body_id` is its index in that
/// seated list. This is what every body_id consumer indexes.
#[test]
fn a_wrapper_the_seat_reorders_welds_row_index_to_member_index() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let (ok, ok_or_tail, carved) = {
        let types = world.types_mut();
        let any = types.any();
        let int = types.int();
        let ok = types.atom_lit("ok");
        let tail = types.atom_lit("tail");
        let ok_or_tail = types.union(ok, tail);
        let any_pair = types.tuple(&[any, any]);
        let int_pair = types.tuple(&[int, int]);
        let carved = types.difference(any_pair, int_pair);
        (ok, ok_or_tail, carved)
    };
    // Edge 0 carries the WIDE surface, edge 1 the NARROW one, so if the
    // result kept edge-list order it would read [0, 1]; a reorder that
    // puts the narrow member first reads [1, 0].
    let edges = [
        wrapper_edge(&mut world, vec![ok_or_tail, carved]),
        wrapper_edge(&mut world, vec![ok, carved]),
    ];

    let selection = construction_member_selection(world.types_mut(), &edges).expect("selection should compile");
    assert_eq!(
        selection.members,
        vec![1, 0],
        "the narrow member `[:ok, carved]` is seated FIRST though it is edge 1, so the seat reordered \
             the member list off the edge order -- the case the corpus's 117 selections never force",
    );
    let plan = selection
        .plan
        .expect("two members the runtime can tell apart need a plan");
    assert_eq!(
        plan.outcomes
            .iter()
            .map(|outcome| outcome.body_id as usize)
            .collect::<Vec<_>>(),
        (0..selection.members.len()).collect::<Vec<_>>(),
        "even under a reorder the weld holds: row i's body_id is i, indexing the SEATED member list",
    );
}

/// fz-kdt.179 drop-to-one: THREE nested members collapse to ONE, so the
/// wrapper calls the survivor directly. `[int]` and `[int | :a]` each pass
/// `[int | :a | :b]`'s head test while naming less than it, and neither
/// covers it, so the seat would never put either ahead of it and the drop
/// takes BOTH -- reaching the `members.len() <= 1 => plan None` path from a
/// three-member wrapper, which no source fixture forces (every list-recursive
/// construction wrapper fz mints carries a separated empty-list member that
/// survives, so the corpus floor is two, never one).
#[test]
fn a_wrapper_whose_three_members_all_stand_in_for_one_drops_to_it() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let (narrow, middle, wide) = {
        let types = world.types_mut();
        let int = types.int();
        let a = types.atom_lit("a");
        let b = types.atom_lit("b");
        let int_a = types.union(int, a);
        let int_a_b = types.union(int_a, b);
        (types.list(int), types.list(int_a), types.list(int_a_b))
    };
    let edges = [
        wrapper_edge(&mut world, vec![narrow]),
        wrapper_edge(&mut world, vec![middle]),
        wrapper_edge(&mut world, vec![wide]),
    ];

    let selection = construction_member_selection(world.types_mut(), &edges).expect("selection should compile");
    assert_eq!(
        selection.members,
        vec![2],
        "`[int]` and `[int | :a]` both pass `[int | :a | :b]`'s head test and name less, so the drop \
             takes both and only the widest member is left",
    );
    assert!(
        selection.plan.is_none(),
        "one member left after a three-member drop is one destination, called directly with no plan",
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
    world
        .types_mut()
        .define_test_callable(ClosureTarget(66), "closure_a", 1);
    world
        .types_mut()
        .define_test_callable(ClosureTarget(68), "closure_b", 1);
    let closure_a = world.types_mut().closure_lit(ClosureTarget(66), Vec::new(), 1);
    let closure_b = world.types_mut().closure_lit(ClosureTarget(68), Vec::new(), 1);
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
            boundary_input_demands: Box::new([]),
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
            boundary_input_demands: Box::new([]),
        },
    ];
    let plan = construction_member_selection(world.types_mut(), &edges)
        .expect("callable flow dispatch should compile")
        .plan
        .expect("distinct callable correlations should produce a plan");
    assert_ne!(
        world.types().runtime_type_predicate(&closure_a),
        world.types().runtime_type_predicate(&closure_b),
        "distinct callables are distinct runtime-observable predicates",
    );
    assert!(
        plan.graph
            .nodes
            .iter()
            .any(|node| matches!(node, DispatchNode::Test { .. })),
        "callable-flow dispatch must ask which callable arrived",
    );
    let reachability = calculate_dispatch_reachability(world.types_mut(), &plan, &[closure_b]);
    let bodies = plan
        .outcomes
        .iter()
        .enumerate()
        .filter(|(index, _)| {
            reachability
                .outcomes
                .contains(&crate::dispatch_matrix::OutcomeId(*index as u32))
        })
        .map(|(_, outcome)| outcome.body_id)
        .collect::<Vec<_>>();
    assert_eq!(
        bodies,
        vec![1],
        "the member keyed on the callable that arrived is the one that runs",
    );
}

/// fz-kdt.141, the instrument gate: a stress that cannot move an order
/// proves nothing about it.
///
/// Three arms on three DISTINCT questions, so `question_groups` gives three
/// groups of one and the retired knob's within-group mirror is the
/// IDENTITY. What is left over is what a seed has to reach.
///
/// THE SUBJECT IS fz-kdt.131's class, and it has to be. Three lists whose
/// HEADS overlap pairwise while no surface contains another -- `[int|:ok]`,
/// `[int|:tail]`, `[:ok|:tail]`, each pair meeting on one element type and
/// disagreeing about the other. Every pair is reached by a common value
/// (`[1]`, `[:ok]`, `[:tail]` respectively), so [`seating`] answers
/// `Escaping` both ways, [`specificity_order`] declines to have an opinion,
/// and the canonical repair may not touch it either: fz-kdt.194's tie-break
/// is for pairs no value reaches both of, and these are the opposite.
/// Arrival order therefore stands all the way through to the plan, which is
/// exactly the residue that must stay perturbable.
///
/// A seed moves it. That is the whole difference fz-kdt.141 buys, and it is
/// measured here rather than argued. Three exact ATOM arms used to be the
/// subject; the atom sets are DISJOINT, so those three arms are pairwise
/// separated and fz-kdt.194's repair now settles them from any arrival --
/// a stress that can no longer move them cannot prove anything about the
/// residue that remains.
#[test]
fn a_seed_moves_an_arrival_order_the_group_reversal_cannot() {
    use dispatch_stress::{DispatchStressed, setting};

    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let ok = world.types_mut().atom_lit("ok");
    let tail = world.types_mut().atom_lit("tail");
    let int_or_ok = world.types_mut().union(int, ok);
    let int_or_tail = world.types_mut().union(int, tail);
    let ok_or_tail = world.types_mut().union(ok, tail);
    let alpha = world.types_mut().list(int_or_ok);
    let beta = world.types_mut().list(int_or_tail);
    let gamma = world.types_mut().list(ok_or_tail);
    let tag = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "tag_impl", 1);
    let target = |atom| CallTargetSummary {
        callee: SelectedCallee::Function(tag),
        surface_inputs: vec![atom],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let arrived = vec![target(alpha), target(beta), target(gamma)];
    {
        let questions = target_questions(world.types_mut(), &arrived);
        let observable = observable_inputs(world.types_mut(), &target_surfaces(&arrived));
        let types = world.types();
        for (x, y) in [(0, 1), (0, 2), (1, 2)] {
            assert_eq!(
                seating(types, &questions, &observable, &[x], &[y]),
                Seating::Escaping,
                "arm {x} and arm {y} share an element type, so a value reaches both and neither \
                     surface names everything the other holds -- fz-kdt.131's class, which no \
                     canonical order may decide",
            );
        }
    }
    let summary = CallSiteSummary {
        targets: arrived.clone(),
        return_ty: None,
    };
    let seated = |world: &mut World| {
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("three arms the atom tests separate are three destinations");
        };
        dispatch.targets
    };

    assert_eq!(
        seated(&mut world),
        arrived,
        "the settled order is what production seats"
    );

    let reversed = {
        let _stress = DispatchStressed::install(setting("arms:reverse"));
        seated(&mut world)
    };
    assert_eq!(
        reversed, arrived,
        "the retired knob mirrors within a question group, and three arms asking three \
             questions are three groups of one -- so it cannot move this callsite at all",
    );

    let permuted = {
        let _stress = DispatchStressed::install(setting("arms:1"));
        seated(&mut world)
    };
    assert_ne!(
        permuted, arrived,
        "a seeded permutation must reach the arrival-decided residue the group mirror leaves \
             untouched, or the corpus is green by construction rather than by safety",
    );
    assert_eq!(
        {
            let mut sorted = permuted
                .iter()
                .map(|target| target.surface_inputs[0])
                .collect::<Vec<_>>();
            sorted.sort();
            sorted
        },
        {
            let mut sorted = arrived
                .iter()
                .map(|target| target.surface_inputs[0])
                .collect::<Vec<_>>();
            sorted.sort();
            sorted
        },
        "a perturbation permutes the arms; it never invents or loses one",
    );
}

/// fz-kdt.141 / fz-kdt.118: off is off, and provably so.
///
/// `""` and `"0"` are the unset setting, and under it `arrival_order`
/// BORROWS -- production allocates nothing, compares nothing and reorders
/// nothing, which is the inertness claim stated where the compiler can
/// check it rather than in prose.
#[test]
fn no_setting_asks_for_anything_but_the_settled_order() {
    use dispatch_stress::{DispatchStress, DispatchStressed, setting};

    let settled = DispatchStress::default();
    for off in ["", "0", "  ", ",", "0,0"] {
        assert_eq!(setting(off), settled, "{off:?} must be the settled order");
    }

    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let atom = world.types_mut().atom_lit("ok");
    let callee = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "impl", 1);
    let target = |ty| CallTargetSummary {
        callee: SelectedCallee::Function(callee),
        surface_inputs: vec![ty],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let targets = vec![target(int), target(atom)];

    assert!(
        matches!(arrival_order(world.types_mut(), &targets), Cow::Borrowed(_)),
        "with no setting the arms are borrowed, not permuted",
    );
    let _stress = DispatchStressed::install(setting("arms:1"));
    assert!(
        matches!(arrival_order(world.types_mut(), &targets), Cow::Owned(_)),
        "a seed is what makes production build a different order at all",
    );
}

/// fz-kdt.141: every seed names a permutation, and never the settled one.
///
/// The second half is the measured one. Most of the corpus's free orders
/// are two items long -- 19 of the 27 arm-perturbable fixtures and every
/// wrapper-bearing one but three -- and a fair shuffle of two items comes
/// out settled about half the time, so a knob without this property reads
/// green on half its seeds for the reason it was built to rule out.
#[test]
fn every_seed_names_a_permutation_and_never_the_settled_one() {
    for len in 0..12usize {
        for seed in 1..40u64 {
            let order = dispatch_stress::seeded_order(seed, len);
            let mut seen = order.clone();
            seen.sort_unstable();
            assert_eq!(
                seen,
                (0..len).collect::<Vec<_>>(),
                "seed {seed} at length {len} must name each slot exactly once",
            );
            assert!(
                len < 2 || order != (0..len).collect::<Vec<_>>(),
                "seed {seed} at length {len} left the order it was asked to perturb",
            );
        }
    }
}

/// fz-kdt.141: a setting names a surface and a perturbation, and anything
/// else is a sweep that measures nothing.
#[test]
fn a_setting_names_a_surface_and_a_perturbation() {
    use dispatch_stress::{DispatchStress, Perturbation, setting};

    assert_eq!(setting("7"), DispatchStress::both(Perturbation::Seeded(7)));
    assert_eq!(setting("reverse"), DispatchStress::both(Perturbation::Reversed));
    assert_eq!(
        setting("arms:reverse"),
        DispatchStress {
            arms: Perturbation::Reversed,
            wrappers: Perturbation::Settled,
        },
    );
    assert_eq!(
        setting("wrappers:3"),
        DispatchStress {
            arms: Perturbation::Settled,
            wrappers: Perturbation::Seeded(3),
        },
    );
    assert_eq!(
        setting("arms:3,wrappers:9"),
        DispatchStress {
            arms: Perturbation::Seeded(3),
            wrappers: Perturbation::Seeded(9),
        },
    );
    for nonsense in ["arms", "wrappers:", "arms:0", "elsewhere:3", "arms:backwards"] {
        assert!(
            std::panic::catch_unwind(|| setting(nonsense)).is_err(),
            "{nonsense:?} must fail loudly: a stress that sweeps inertly reads as green",
        );
    }
}

/// fz-kdt.194 REVIEW PROBE (attack 1, on the design itself): the NAIVE reading of
/// the ticket -- fold the canonical tie-break into `seats_before` as an
/// extra disjunct and let the backward insertion pass use it -- SILENTLY
/// LOSES A COVERING SEAT, and `every_inversion_covers` does not catch it.
///
/// Three single-input arms, each input a 2-tuple:
///
/// ```text
///     Q  {[int],      :s}
///     R  {[int|:ok],  :s}    R covers Q: same question, strictly wider surface
///                            on an ERASING axis (the list behind the tag)
///     P  {[int|:bb],  :t}    separated from both at tuple position 1 (:t vs :s)
/// ```
///
/// with `key(Q) < key(P) < key(R)` under typed activation order. Arrival `[P, Q, R]`.
///
/// - The LANDED shape (insertion pass, then adjacent-transposition repair)
///   keeps `R` ahead of `Q`: the covering seat the insertion pass made
///   survives, because a swap only ever exchanges the pair it is about.
/// - The NAIVE shape lets `Q` walk left past `P` on the tie-break, which
///   puts `P` between `R` and the prefix -- so `R` stops at `P` and never
///   reaches `Q` at all. `Q` comes out ahead of `R`, a pair
///   `seating` calls `Escaping`, and the two were never compared.
/// - `every_inversion_covers` accepts the naive result, because `Q` before
///   `R` is ARRIVAL order and therefore not an inversion.
#[test]
fn a_tie_break_folded_into_the_seat_loses_a_covering_seat() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let bb = world.types_mut().atom_lit("bb");
    let ok = world.types_mut().atom_lit("ok");
    let s = world.types_mut().atom_lit("s");
    let t = world.types_mut().atom_lit("t");
    let int_or_ok = world.types_mut().union(int, ok);
    let int_or_bb = world.types_mut().union(int, bb);
    let int_list = world.types_mut().list(int);
    let ok_list = world.types_mut().list(int_or_ok);
    let bb_list = world.types_mut().list(int_or_bb);
    let q_ty = world.types_mut().tuple(&[int_list, s]);
    let r_ty = world.types_mut().tuple(&[ok_list, s]);
    let p_ty = world.types_mut().tuple(&[bb_list, t]);
    let callee = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "step", 1);
    let target = |ty| CallTargetSummary {
        callee: SelectedCallee::Function(callee),
        surface_inputs: vec![ty],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    // arrival [P, Q, R]
    let arms = [target(p_ty), target(q_ty), target(r_ty)];
    let observable = observable_inputs(world.types_mut(), &target_surfaces(&arms));
    let questions = runtime_questions(world.types_mut(), &observable);
    let groups = grouped_by_question(&questions);
    let types = world.types();
    assert_eq!(groups, vec![vec![0], vec![1], vec![2]], "three singleton groups");
    let (p, q, r) = (0usize, 1usize, 2usize);
    let keys = groups
        .iter()
        .map(|group| canonical_key(types, &observable, group))
        .collect::<Vec<_>>();
    // The shape this witness needs. If any precondition stops holding the
    // witness has to be rebuilt, so assert them rather than assume them.
    assert_eq!(
        seating(types, &questions, &observable, &groups[p], &groups[q]),
        Seating::Separated,
        "P and Q ask disjoint tuple tags at position 1",
    );
    assert_eq!(
        seating(types, &questions, &observable, &groups[p], &groups[r]),
        Seating::Separated,
        "P and R ask disjoint tuple tags at position 1",
    );
    assert_eq!(
        seating(types, &questions, &observable, &groups[r], &groups[q]),
        Seating::Covering,
        "R's surface contains Q's on the erasing position, so the seat MUST put R first",
    );
    assert_eq!(
        seating(types, &questions, &observable, &groups[q], &groups[r]),
        Seating::Escaping,
        "and the other direction is a blind escape -- Q ahead of R is what must not happen",
    );
    assert_eq!(
        types.cmp_activation_tys(&observable[keys[q]], &observable[keys[p]]),
        Ordering::Less,
        "key(Q) < key(P)",
    );
    assert_eq!(
        types.cmp_activation_tys(&observable[keys[p]], &observable[keys[r]]),
        Ordering::Less,
        "key(P) < key(R)",
    );

    // READING B, what landed.
    let landed = specificity_order(types, &questions, &observable);
    let position = |order: &[usize], arm: usize| order.iter().position(|a| *a == arm).unwrap();
    assert!(
        position(&landed, r) < position(&landed, q),
        "the landed shape keeps the covering seat: R before Q, order {landed:?}",
    );

    // READING A, the naive fold, rebuilt here exactly as the ticket's
    // wording admits it.
    let naive = {
        let naive_before = |x: usize, y: usize| {
            seats_before(types, &questions, &observable, &groups[x], &groups[y])
                || (matches!(
                    seating(types, &questions, &observable, &groups[x], &groups[y]),
                    Seating::Separated
                ) && types.cmp_activation_tys(&observable[keys[x]], &observable[keys[y]]) == Ordering::Less)
        };
        let mut seated: Vec<usize> = Vec::new();
        for group in 0..groups.len() {
            let mut at = seated.len();
            while at > 0 && naive_before(group, seated[at - 1]) {
                at -= 1;
            }
            seated.insert(at, group);
        }
        seated
    };
    assert!(
        position(&naive, q) < position(&naive, r),
        "THE NAIVE READING IS UNSAFE: Q comes out ahead of R, a pair the seat calls Escaping, \
             and the two were never compared -- the tie-break moved Q out of R's insertion walk. \
             order {naive:?}",
    );
    assert!(
        every_inversion_covers(types, &questions, &observable, &groups, &naive),
        "and the standing law does NOT catch it: Q before R is ARRIVAL order, so it is not an \
             inversion, and the escape fix is lost silently",
    );
}

/// fz-kdt.194 REVIEW PROBE (attack 2, on the doc's account of the limit): the
/// residual arrival-dependence the repair leaves is NOT confined to
/// fz-kdt.107's and fz-kdt.131's classes. A COVERING pair -- one the seat
/// itself decided, and whose order is therefore already a function of the
/// arm set -- can sit between two separated groups and block the repair
/// just as an `Escaping` pair does.
///
/// Same three arms as probe 1. `R` covers `Q`; `P` is separated from both;
/// `key(Q) < key(P) < key(R)`.
///
/// ```text
///     arrival [P, Q, R]  ->  seat [P, R, Q]  ->  repair [P, R, Q]
///     arrival [Q, R, P]  ->  seat [R, Q, P]  ->  repair [R, Q, P]
/// ```
///
/// Both are safe -- `R` is ahead of `Q` in both, which is the whole seat
/// obligation -- and both leave `P` where the seat's own walk stopped. But
/// they are DIFFERENT artifacts, and the pair that blocked the repair from
/// reconciling them is the `Covering` one, not a residue anybody owns.
///
/// This is why [`canonically_order_separated_neighbours`]'s doc and
/// `.agent/docs/dispatch-matrix.md` state the limit as "pairwise separated
/// END TO END" and not as "blocked only by a pair whose order means
/// something". The first draft of both said the latter, and this gate is
/// what refuted it.
#[test]
fn a_covering_pair_blocks_the_repair_and_leaves_the_arrival_showing() {
    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let int = world.types_mut().int();
    let bb = world.types_mut().atom_lit("bb");
    let ok = world.types_mut().atom_lit("ok");
    let s = world.types_mut().atom_lit("s");
    let t = world.types_mut().atom_lit("t");
    let int_or_ok = world.types_mut().union(int, ok);
    let int_or_bb = world.types_mut().union(int, bb);
    let int_list = world.types_mut().list(int);
    let ok_list = world.types_mut().list(int_or_ok);
    let bb_list = world.types_mut().list(int_or_bb);
    let q_ty = world.types_mut().tuple(&[int_list, s]);
    let r_ty = world.types_mut().tuple(&[ok_list, s]);
    let p_ty = world.types_mut().tuple(&[bb_list, t]);
    // THREE callees, so `unroutable_alternatives`' same-callee conjunct
    // keeps the drop out of this witness; only the seat is under test.
    let p_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "p_impl", 1);
    let q_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "q_impl", 1);
    let r_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "r_impl", 1);
    let target = |function, ty| CallTargetSummary {
        callee: SelectedCallee::Function(function),
        surface_inputs: vec![ty],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let seated = |world: &mut World, arrival: &[CallTargetSummary]| {
        let summary = CallSiteSummary {
            targets: arrival.to_vec(),
            return_ty: None,
        };
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("three distinguishable arms are three destinations");
        };
        dispatch.targets
    };
    let (p, q, r) = (target(p_fn, p_ty), target(q_fn, q_ty), target(r_fn, r_ty));
    let forwards = seated(&mut world, &[p.clone(), q.clone(), r.clone()]);
    let backwards = seated(&mut world, &[q.clone(), r.clone(), p]);
    let at = |order: &[CallTargetSummary], arm: &CallTargetSummary| {
        order
            .iter()
            .position(|target| target == arm)
            .expect("every arm survives")
    };
    assert!(
        at(&forwards, &r) < at(&forwards, &q),
        "the covering seat holds either way"
    );
    assert!(
        at(&backwards, &r) < at(&backwards, &q),
        "the covering seat holds either way"
    );
    assert_ne!(
        forwards, backwards,
        "and yet the two arrivals render DIFFERENT arm orders, with no fz-kdt.107 or fz-kdt.131 \
             pair anywhere in the callsite: the blocker is the COVERING pair",
    );
}

/// fz-kdt.194 REVIEW PROBE (attack 3, on the re-homing of
/// `a_seed_moves_an_arrival_order_the_group_reversal_cannot`): the OLD
/// subject really is settled by the repair, so the re-homing is honest
/// rather than a way to hide a lost instrument.
///
/// Three exact-atom arms, pairwise disjoint. Under fz-kdt.194 they are
/// pairwise SEPARATED all the way through, so the repair reaches one order
/// from every arrival -- which is exactly what makes them useless as a
/// perturbable residue, and why that instrument had to be re-homed on
/// fz-kdt.131's class. It is also the positive statement of the repair's
/// reach at unit scale: an end-to-end separated run settles, from all six
/// seeds and from the group reversal.
#[test]
fn three_disjoint_atom_arms_settle_to_one_order_from_every_arrival() {
    use dispatch_stress::{DispatchStressed, setting};

    let _tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    let alpha = world.types_mut().atom_lit("alpha");
    let beta = world.types_mut().atom_lit("beta");
    let gamma = world.types_mut().atom_lit("gamma");
    let tag = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "tag_impl", 1);
    let target = |atom| CallTargetSummary {
        callee: SelectedCallee::Function(tag),
        surface_inputs: vec![atom],
        activation: None,
        activation_inputs: None,
        extern_params: None,
        return_ty: None,
    };
    let arrived = vec![target(alpha), target(beta), target(gamma)];
    {
        let questions = target_questions(world.types_mut(), &arrived);
        let observable = observable_inputs(world.types_mut(), &target_surfaces(&arrived));
        let types = world.types();
        for (x, y) in [(0, 1), (0, 2), (1, 2)] {
            assert_eq!(
                seating(types, &questions, &observable, &[x], &[y]),
                Seating::Separated,
                "three disjoint atoms are pairwise separated",
            );
        }
    }
    let summary = CallSiteSummary {
        targets: arrived,
        return_ty: None,
    };
    let seated = |world: &mut World| {
        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("three arms the atom tests separate are three destinations");
        };
        dispatch.targets
    };
    let settled = seated(&mut world);
    for stress in [
        "arms:1",
        "arms:2",
        "arms:3",
        "arms:4",
        "arms:5",
        "arms:6",
        "arms:reverse",
    ] {
        let permuted = {
            let _stress = DispatchStressed::install(setting(stress));
            seated(&mut world)
        };
        assert_eq!(
            permuted, settled,
            "{stress} no longer moves the old subject -- the instrument would have been \
                 toothless there, so the re-homing is honest",
        );
    }
}
