//! What a plan asks, and in what order.

use super::*;
use crate::compiler2::World;
use crate::dispatch_matrix::{DispatchNode, Region, SubjectId, SubjectSource};
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
