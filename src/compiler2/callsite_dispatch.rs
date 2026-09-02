use std::borrow::Cow;

use crate::ast::{Pattern, Spanned};
use crate::dispatch_matrix::pattern::{
    PatternBodyId, PatternDispatchError, PatternDispatchPlan, PatternRow, PatternSubjectRef, SourcePatternRows,
    pattern_dispatch_from_source,
};
use crate::runtime_type_predicate::RuntimeTypePredicate;
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
///
/// What survives is then SEATED by [`specificity_order`], which corrects
/// arrival order wherever the arms themselves say it routes a value into a
/// body that never named it.
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
/// surface its runtime questions are asked about, in the order the plan tests
/// them.
fn routable_alternatives(types: &mut Types, targets: &[CallTargetSummary]) -> (Vec<CallTargetSummary>, Vec<Vec<Ty>>) {
    let observable_inputs = targets
        .iter()
        .map(|target| runtime_dispatch_inputs(types, &target.surface_inputs))
        .collect::<Vec<_>>();
    let groups = question_groups(types, targets);
    let unroutable = unroutable_alternatives(types, targets, &observable_inputs, &groups);
    let (routable, observable): (Vec<_>, Vec<_>) = targets
        .iter()
        .cloned()
        .zip(observable_inputs)
        .enumerate()
        .filter(|(index, _)| !unroutable.contains(index))
        .map(|(_, alternative)| alternative)
        .unzip();
    let order = specificity_order(types, &routable, &observable);
    (permuted(routable, &order), permuted(observable, &order))
}

/// The order a callsite tests its arms in: arrival order, corrected wherever
/// the arms themselves say it is wrong to.
///
/// Arm order used to be the settled targets' order and nothing else, which is
/// the semantic fixpoint's, which is the agenda's -- so one dispatch's arms
/// swapped positions between two legal schedules and the artifact stopped
/// being a function of the program (fz-kdt.129).
///
/// # What a seat can get wrong
///
/// An arm's `RuntimeTypePredicate` is COARSER than the surface its body was
/// compiled for: a list head says nothing about the tail, and a tuple position
/// erases whatever its own sub-test erases. So a value can satisfy every
/// question an arm asks and still lie outside that arm's surface. Seat such an
/// arm first and the value lands in a body whose representation never named it
/// -- `fz_list_head_int_ref` reads a list of atoms as a list of ints and aborts
/// on the JIT and native doors, while the interpreter's dynamic tags hide it.
///
/// Call that a BLIND ESCAPE: `early` is seated before `late`, and at some
/// position the two ask the runtime a question that cannot separate them,
/// while `late`'s surface holds values `early`'s does not. Both of the
/// orderings tried before this one create blind escapes, in opposite
/// directions (the examples below are as they were measured, when a list test
/// still saw empty-or-cons and nothing else):
///
/// - seating the narrower SURFACE first (fz-kdt.129's first candidate, refuted
///   by measurement) puts `list(int) x {all?/1, all?/2, empty?}` ahead of
///   `list(:ok) x {empty?}`, and the wider callable test swallows the
///   sibling's values;
/// - seating the narrower TEST first (fz-kdt.129's first build, refuted by
///   `dispatch_seat_element_blind` and this file's unit gates) puts
///   `list(int) x {all?/1}` ahead of `list(:ok) x {all?/1, empty?}` because
///   its callable SET is strictly smaller -- and `[:ok, :ok]` carrying
///   `all?/1` satisfied BOTH its questions and reached the int-reading body.
///   fz-kdt.107 step 3 gave those two arms disjoint HEAD questions, so that
///   particular pair no longer meets on an erasing axis; the law the pair
///   taught stands unchanged.
///
/// Neither containment is the criterion on its own. SURFACE COVERAGE is:
/// [`covers`] holds of `(early, late)` when, at every position where their
/// tests could both admit a value on an ERASING axis
/// (`overlaps_on_an_erasing_axis` -- list tails, tuple payloads, struct/
/// map/binary/resource contents), `early`'s surface already contains
/// `late`'s. "The tests differ" is NOT separation on those axes -- arities
/// {2} and {2,3} both admit a 2-tuple -- so difference alone never excuses
/// the surface check; only exact axes (ints, floats, atoms, callables) can,
/// because a value passes an exact test only by being in the tested set,
/// which the arm's surface names. Under that definition, seating a covering
/// arm first cannot escape anything, by construction.
///
/// # The rule
///
/// Arms are seated by their question GROUP, and a group's members keep arrival
/// order. That carve-out is fz-kdt.107's: nothing the runtime emits separates
/// a group's members, so which one comes first decides which body their shared
/// values run, and re-deciding it is a miscompile -- fz-kdt.107 prototyped
/// canonically ordering them and got `{:done, 3}` where `{:halted, 3}` was due.
///
/// Groups start in arrival order. Group `x` is moved ahead of group `y` when
///
/// ```text
///     covers(x, y)  and  ( not covers(y, x)  or  test(x) strictly inside test(y) )
/// ```
///
/// -- the first disjunct is the OBLIGATION (only one direction is escape-free,
/// so take it), the second is the PRECISION preference fz-kdt.129 asked for
/// (both directions are escape-free, so hand a value both tests admit to the
/// arm that named it most precisely). The relation is antisymmetric: if both
/// directions held, both would need `covers` both ways, so both would rest on
/// strict mutual containment of the tests -- which makes the tests equal and
/// the two groups one.
///
/// Where NEITHER group covers the other, no seat is escape-free and this rule
/// declines to have an opinion: the pair keeps arrival order. That is the
/// fz-kdt.107 inseparable class one rung wider, it is a standing hazard of
/// arrival order that predates this rule, and fz-kdt.131 owns it -- the cure
/// is a runtime test that can see what the body relies on (fz-kdt.119's tuple
/// tags, fz-kdt.107's list elements), not a cleverer sort.
///
/// # Why the result is a seat, and a safe one
///
/// The correction is one backward insertion pass: each group walks left past
/// already-seated groups for as long as the relation above holds of the pair,
/// and stops at the first group it may not pass. A permutation comes out, so
/// the seat is TOTAL by construction and needs no tie-break to fall through
/// to; it is a deterministic function of the arms and their arrival order; and
/// stopping at the first refusal is not a compromise but a requirement,
/// because passing a group means passing everything between.
///
/// The safety argument is the point of building it this way. Every pair whose
/// seat differs from arrival order was individually checked and moved only
/// under `covers`, which admits no blind escape; every other pair sits exactly
/// as arrival left it. So the seat's blind escapes are a SUBSET of arrival
/// order's -- this rule can only ever remove them, never add one. The
/// `debug_assert` below holds every callsite of every debug compile to it, and
/// `compiler2_dispatch_seats_the_covering_arm_where_one_covers` reads the same
/// property back off the landed artifact.
///
/// `covers` is not transitive (two groups can be blind at different positions),
/// so no rank or comparator linearizes it; that is why the pass is an explicit
/// insertion rather than a sort, and why a blocked move leaves arrival order
/// standing instead of forcing an order the arms do not justify.
fn specificity_order(types: &mut Types, targets: &[CallTargetSummary], observable: &[Vec<Ty>]) -> Vec<usize> {
    let groups = question_groups(types, targets);
    if groups.len() < 2 {
        return (0..targets.len()).collect();
    }
    let questions = runtime_questions(types, targets);
    let types = &*types;
    let seats_before = |x: &Vec<usize>, y: &Vec<usize>| {
        covers(types, &questions, observable, x, y)
            && (!covers(types, &questions, observable, y, x) || strictly_inside(&questions, x, y))
    };
    let mut seated: Vec<usize> = Vec::with_capacity(groups.len());
    for group in 0..groups.len() {
        let mut at = seated.len();
        while at > 0 && seats_before(&groups[group], &groups[seated[at - 1]]) {
            at -= 1;
        }
        seated.insert(at, group);
    }
    debug_assert!(
        every_inversion_covers(types, &questions, observable, &groups, &seated),
        "a seat moved a group ahead of one whose surface it does not cover, so a value the plan admits \
         now reaches a body arrival order would have kept it out of",
    );
    seated.into_iter().flat_map(|group| groups[group].clone()).collect()
}

/// Whether the seat added no blind escape: every group it moved ahead of a
/// group that ARRIVED before it covers that group's surface.
///
/// This is the whole safety claim, checked against the permutation itself
/// rather than against the reasoning that produced it. Pairs the seat left in
/// arrival order are not this rule's business -- they escape, or not, exactly
/// as they did before any seating rule existed (fz-kdt.131).
fn every_inversion_covers(
    types: &Types,
    questions: &[Vec<RuntimeTypePredicate>],
    observable: &[Vec<Ty>],
    groups: &[Vec<usize>],
    seated: &[usize],
) -> bool {
    seated.iter().enumerate().all(|(rank, early)| {
        seated[rank + 1..]
            .iter()
            .all(|late| early < late || covers(types, questions, observable, &groups[*early], &groups[*late]))
    })
}

/// Whether seating `early` before `late` can route a value into a body that
/// never named it.
///
/// Position by position: either the two groups ask DIFFERENT questions there,
/// and the plan's own test is what keeps `late`'s values out of `early`; or
/// they ask the same question, the test is blind, and `early`'s surface must
/// already contain every value `late`'s holds. A group is a set of arms one
/// question cannot separate, so the surface half is checked across the whole
/// product: whichever member arrival puts first receives the values, and every
/// member of `late` may arrive at it.
///
/// This is the one containment a seat may be reasoned from. Containment of the
/// TESTS is not it -- a test is a projection and it drops what the body reads.
/// Containment of the SURFACES is not it either -- a surface says nothing
/// about which values the emitted test will actually hand over.
fn covers(
    types: &Types,
    questions: &[Vec<RuntimeTypePredicate>],
    observable: &[Vec<Ty>],
    early: &[usize],
    late: &[usize],
) -> bool {
    let (early_asks, late_asks) = (&questions[early[0]], &questions[late[0]]);
    if early_asks.len() != late_asks.len() {
        return false;
    }
    (0..early_asks.len()).all(|position| {
        !early_asks[position].overlaps_on_an_erasing_axis(&late_asks[position])
            || late.iter().all(|late| {
                early
                    .iter()
                    .all(|early| types.is_subtype(&observable[*late][position], &observable[*early][position]))
            })
    })
}

/// Whether every value `narrow`'s group's test admits, `wide`'s admits too,
/// and not the other way about.
///
/// One group is one question, so a group's test is any member's.
fn strictly_inside(questions: &[Vec<RuntimeTypePredicate>], narrow: &[usize], wide: &[usize]) -> bool {
    let inside = |narrow: &[RuntimeTypePredicate], wide: &[RuntimeTypePredicate]| {
        narrow.len() == wide.len() && narrow.iter().zip(wide).all(|(narrow, wide)| narrow.contained_in(wide))
    };
    let (narrow, wide) = (&questions[narrow[0]], &questions[wide[0]]);
    inside(narrow, wide) && !inside(wide, narrow)
}

/// The items an order names, in the order it names them.
fn permuted<T>(items: Vec<T>, order: &[usize]) -> Vec<T> {
    let mut slots = items.into_iter().map(Some).collect::<Vec<_>>();
    order
        .iter()
        .map(|index| slots[*index].take().expect("an arm order names each arm exactly once"))
        .collect()
}

/// Whether `wide`'s alternative can supply `narrow`'s: the same callee, on an
/// observable domain that contains it.
///
/// The same-callee conjunct is load-bearing: a multi-target callsite normally
/// names one target per SELECTED CALLEE -- that is what protocol dispatch is
/// (`jobs/semantic.rs` settles one `CallTargetSummary` per viable impl) -- and
/// a wider domain sitting on ANOTHER function's body is no stand-in at all.
///
/// Strictness is what makes the relation antisymmetric, and both halves are
/// transitive.
fn stands_in_for(
    types: &Types,
    targets: &[CallTargetSummary],
    observable: &[Vec<Ty>],
    wide: usize,
    narrow: usize,
) -> bool {
    targets[wide].callee == targets[narrow].callee
        && observable[wide].len() == observable[narrow].len()
        && observable[wide]
            .iter()
            .zip(&observable[narrow])
            .all(|(wide, narrow)| types.is_subtype(narrow, wide))
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
    let questions = runtime_questions(types, targets);
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

/// The question each target puts to the runtime: one `RuntimeTypePredicate`
/// per input, projected from the observable surface.
///
/// This is what the plan's emitted tests actually ask. It is coarser than the
/// observable surface it is projected from -- `[int]` and `[int | :ok]` put
/// one and the same question to a cons cell's first element, and disagree only
/// about a tail no test reads -- which is why it, and not the surface, is what
/// a routing may be reasoned from.
fn runtime_questions(types: &mut Types, targets: &[CallTargetSummary]) -> Vec<Vec<RuntimeTypePredicate>> {
    targets
        .iter()
        .map(|target| {
            runtime_dispatch_inputs(types, &target.surface_inputs)
                .iter()
                .map(|ty| types.runtime_type_predicate(ty))
                .collect::<Vec<_>>()
        })
        .collect()
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
/// [`stands_in_for`] is judged on OBSERVABLE surfaces, not settled semantic
/// ones (fz-kdt.118). Alternatives of equal denotation are never each other's
/// excuse for disappearing, and the relation is transitive, so an alternative
/// dropped only because of another dropped one is dropped by that one's own
/// twin too, and no cascade is needed.
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
    let stands_in = |wide: usize, narrow: usize| stands_in_for(types, targets, observable, wide, narrow);
    groups
        .iter()
        .flat_map(|group| {
            group.iter().copied().filter(|narrow| {
                group
                    .iter()
                    .copied()
                    .any(|wide| wide != *narrow && stands_in(wide, *narrow) && !stands_in(*narrow, wide))
            })
        })
        .collect()
}

/// The order a callsite's settled targets arrive in.
///
/// Arm order is the scheduler's, never the language's: any permutation of a
/// callsite's targets is an order the semantic fixpoint could legally have
/// produced. Production reads the settled order and borrows it; the stress
/// gate hands [`specificity_order`] a different one and asks whether the
/// answer moved.
///
/// What arrives is not always what the plan tests: [`specificity_order`]
/// corrects arrival wherever the arms justify a correction, and it does so
/// deterministically -- a covers-proven inversion is a fact about the arms,
/// not about when they turned up. So permuting arrival does not perturb the
/// seat's own decisions at all; what it perturbs is exactly the RESIDUE the
/// seat declines to decide: the members of one question group, where arrival
/// is the one thing standing between the corpus and a wrong answer
/// (fz-kdt.107), and every pair where neither group covers the other, where no
/// seat is any safer than the one it came with (fz-kdt.131).
fn arrival_order<'a>(types: &mut Types, targets: &'a [CallTargetSummary]) -> Cow<'a, [CallTargetSummary]> {
    match dispatch_stress::arms() {
        dispatch_stress::Perturbation::Settled => Cow::Borrowed(targets),
        dispatch_stress::Perturbation::Reversed => {
            Cow::Owned(dispatch_stress::reverse_indistinguishable_groups(types, targets))
        }
        dispatch_stress::Perturbation::Seeded(seed) => Cow::Owned(permuted(
            targets.to_vec(),
            &dispatch_stress::seeded_order(seed, targets.len()),
        )),
    }
}

/// The schedule-legal perturbations the dispatch-order stress drives with.
///
/// TWO orders decide which body a value reaches, and neither is the language's:
///
/// - a callsite's ARRIVAL order, which is the settled targets' order, which is
///   the semantic fixpoint's, which is the agenda's ([`arrival_order`]);
/// - a callable value's CONSTRUCTION-WRAPPER member order, which is a
///   `BTreeSet<CallableSurface>` walked in interned-id order, which is the type
///   interner's mint order, which is the agenda's again
///   ([`dispatch_from_callable_flow_edges`] and the members beside it).
///
/// Any permutation of either is an order the fixpoint could have delivered, so
/// an answer that moves under one is an answer a schedule decides.
///
/// # Why reversing the indistinguishable groups is not enough
///
/// The retired `FZ_STRESS_REVERSE_DISPATCH_ARMS` mirrored each
/// runtime-indistinguishable GROUP and nothing else. That reaches exactly one
/// permutation, of exactly the pairs the plan cannot separate -- and as
/// fz-kdt.119 taught the predicate to separate more of them, the same knob got
/// weaker: on a callsite whose groups are all singletons it is the IDENTITY, a
/// gate that cannot move a single arm. And it never touched the wrapper order
/// at all (fz-kdt.136).
///
/// A seeded permutation of the WHOLE order has neither limit: it varies every
/// ordering the seat leaves free, on both surfaces, and it is a deterministic
/// function of (seed, length) so a finding replays. Measured over the corpus at
/// the fz-kdt.141 landing: the reversal moves 8 fixtures' artifacts, an arm
/// seed moves 27, a wrapper seed moves 19, and of the four fixtures that abort
/// natively under a legal arm order the reversal reaches ONE.
///
/// # The setting
///
/// `FZ_STRESS_PERMUTE_DISPATCH` names a comma-separated list of clauses, each
/// `<surface>:<perturbation>` or a bare `<perturbation>` meaning both surfaces:
///
/// ```text
///     (unset) | "" | "0"   the settled order, and no code that reads it
///     7                    seed 7 on arms and on wrappers
///     arms:7               seed 7 on arrival order only
///     wrappers:7           seed 7 on construction members only
///     reverse              reverse both surfaces
///     arms:reverse         exactly what the retired knob did
///     arms:3,wrappers:9    a different seed per surface
/// ```
///
/// Seed `0` is off, not a seed -- `""`/`"0"`/unset are one thing (fz-kdt.118),
/// and a setting the grammar does not recognize PANICS rather than sweeping
/// inertly, because a stress that silently measures nothing reads as green.
///
/// The setting is per-thread. A process-wide default comes from the
/// environment, which is how a fixture gets swept through the real `fz2`
/// binary; in-process drivers install [`DispatchStressed`] instead, and because
/// each `cargo test` case owns its thread the perturbation never leaks into a
/// neighbour running beside it.
pub(crate) mod dispatch_stress {
    use std::cell::Cell;

    use super::{CallTargetSummary, CallableFlowEdge, Types, permuted, question_groups};

    /// Names the environment variable that turns a perturbation on for a whole
    /// process, so a fixture can be swept through the real `fz2` binary as well
    /// as driven in-process.
    pub(crate) const PERMUTE_DISPATCH_ENV: &str = "FZ_STRESS_PERMUTE_DISPATCH";

    /// What one surface's order is replaced by.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    pub(crate) enum Perturbation {
        /// The order the fixpoint settled on. Production's, and provably inert:
        /// nothing is cloned, compared or reordered.
        #[default]
        Settled,
        /// Arms: each runtime-indistinguishable group mirrored across the slots
        /// it already occupies -- the retired knob's exact permutation, kept
        /// because the fixtures and prose that measured it name it. Wrappers:
        /// the member list reversed.
        Reversed,
        /// A permutation of the whole order, a pure function of the seed and
        /// the number of items.
        Seeded(u64),
    }

    /// What each surface's order is replaced by.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    pub(crate) struct DispatchStress {
        pub(crate) arms: Perturbation,
        pub(crate) wrappers: Perturbation,
    }

    impl DispatchStress {
        /// The same perturbation on both surfaces.
        pub(crate) fn both(perturbation: Perturbation) -> Self {
            Self {
                arms: perturbation,
                wrappers: perturbation,
            }
        }
    }

    thread_local! {
        static STRESS: Cell<DispatchStress> = Cell::new(setting(
            std::env::var(PERMUTE_DISPATCH_ENV).unwrap_or_default().as_str(),
        ));
    }

    /// The perturbation this thread applies to callsite arrival order.
    pub(crate) fn arms() -> Perturbation {
        STRESS.with(Cell::get).arms
    }

    /// The perturbation this thread applies to construction-wrapper members.
    pub(crate) fn wrappers() -> Perturbation {
        STRESS.with(Cell::get).wrappers
    }

    /// What a setting asks for. Panics on an unrecognized setting -- but a
    /// lazy panic fires only when a perturbation site is reached, which the
    /// fz-kdt.141 refutation measured letting a typo'd sweep read green on
    /// 72% of the corpus. `validate_env` is the eager front door: the CLI
    /// calls it before dispatching any command, so a typo fails EVERY run
    /// with a usage diagnostic instead of only the runs that dispatch.
    pub(crate) fn setting(value: &str) -> DispatchStress {
        try_setting(value).unwrap_or_else(|message| panic!("{message}"))
    }

    /// Eager validation of the environment setting for the CLI front door.
    pub(crate) fn validate_env() -> Result<(), String> {
        try_setting(std::env::var(PERMUTE_DISPATCH_ENV).unwrap_or_default().as_str()).map(|_| ())
    }

    fn try_setting(value: &str) -> Result<DispatchStress, String> {
        let mut stress = DispatchStress::default();
        for clause in value
            .split(',')
            .map(str::trim)
            .filter(|clause| !clause.is_empty() && *clause != "0")
        {
            let (surface, how) = clause.split_once(':').unwrap_or(("", clause));
            let perturbation = perturbation(how).ok_or_else(|| {
                format!("{PERMUTE_DISPATCH_ENV}: {clause:?} names no perturbation -- want `reverse` or a seed above 0")
            })?;
            match surface {
                "" => stress = DispatchStress::both(perturbation),
                "arms" => stress.arms = perturbation,
                "wrappers" => stress.wrappers = perturbation,
                _ => {
                    return Err(format!(
                        "{PERMUTE_DISPATCH_ENV}: {clause:?} names no surface -- want `arms` or `wrappers`"
                    ));
                }
            }
        }
        Ok(stress)
    }

    fn perturbation(how: &str) -> Option<Perturbation> {
        match how {
            "reverse" => Some(Perturbation::Reversed),
            seed => seed
                .parse::<u64>()
                .ok()
                .filter(|seed| *seed != 0)
                .map(Perturbation::Seeded),
        }
    }

    /// Drives both surfaces the way the setting says for as long as it lives,
    /// then puts the previous setting back.
    #[cfg(test)]
    pub(crate) struct DispatchStressed(DispatchStress);

    #[cfg(test)]
    impl DispatchStressed {
        pub(crate) fn install(stress: DispatchStress) -> Self {
            Self(STRESS.with(|current| current.replace(stress)))
        }
    }

    #[cfg(test)]
    impl Drop for DispatchStressed {
        fn drop(&mut self) {
            STRESS.with(|current| current.set(self.0));
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

    /// The construction-wrapper members and the selection plan's rows, in the
    /// order this thread's setting asks for.
    ///
    /// This is the ONE authority: fz-kdt.108 established that a selection row's
    /// `body_id` indexes the parallel member list and must increase
    /// monotonically, so the two are welded and no permutation downstream of
    /// the weld is representable. Permuting the edges themselves, before either
    /// derives, keeps the weld and lets members, selection, boundary
    /// resolutions and the flow's resolution list all inherit one order. It is
    /// called from `jobs/runtime_demand.rs`, where the edges are built.
    ///
    /// WHAT IT CATCHES, measured rather than hoped for (fz-kdt.141). It does
    /// NOT produce fz-kdt.132's `matched no member`, and no ordering can:
    /// reordering makes the dead member live INSTEAD of its sibling, never
    /// alongside it, because the blind tuple test hands every value to
    /// whichever comes first -- and a member that takes everything marshals its
    /// own return form consistently. That break needs the two members reached
    /// by DIFFERENT values, which is fz-kdt.138's exact test, not an order.
    ///
    /// It used to decide the whole 268-escape
    /// `FZ_STRESS_ASSERT_SURFACE_MEMBERSHIP` baseline (268 settled, 68 at
    /// `wrappers:1`, 20 at `wrappers:6`) where arm seeds moved it by zero.
    /// fz-kdt.132 emptied that census by minting the accumulator rung whose
    /// values had no member at all, so the order now decides nothing there:
    /// every setting reads 0. What this perturbation still holds is the law --
    /// which member a value reaches must not change an answer -- and
    /// `compiler2_a_permuted_wrapper_order_reseats_the_construction_members`
    /// proves it still lands on a moved artifact.
    pub(crate) fn perturbed_construction_members(edges: Vec<CallableFlowEdge>) -> Vec<CallableFlowEdge> {
        match wrappers() {
            Perturbation::Settled => edges,
            Perturbation::Reversed => edges.into_iter().rev().collect(),
            Perturbation::Seeded(seed) => {
                let order = seeded_order(seed, edges.len());
                permuted(edges, &order)
            }
        }
    }

    /// A permutation of `len` slots, a pure function of the seed and the
    /// length, and never the settled order.
    ///
    /// Purity is what makes a finding replayable and what keeps a perturbed
    /// fact stable across the recomputations the fixpoint asks for: the same
    /// edges always come back in the same order, so nothing oscillates.
    ///
    /// NEVER SETTLED is the other half, and it is measured rather than
    /// cosmetic: most of the corpus's free orders are two items long, a fair
    /// shuffle of two items comes out settled about half the time, and a seed
    /// that leaves the order it was asked to perturb is a green reading with
    /// nothing behind it -- the fz-kdt.118 lesson one rung further in. So a
    /// draw that lands on the settled order is moved off it by one
    /// transposition, and every seed moves every order of two or more.
    pub(crate) fn seeded_order(seed: u64, len: usize) -> Vec<usize> {
        let mut order = (0..len).collect::<Vec<_>>();
        let mut state = seed ^ (len as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        for slot in (1..len).rev() {
            let pick = (next(&mut state) % (slot as u64 + 1)) as usize;
            order.swap(slot, pick);
        }
        if len > 1 && order.iter().copied().eq(0..len) {
            order.swap(0, 1);
        }
        order
    }

    /// SplitMix64: a full-period mixer, so a seed of 1 is as good as any other.
    fn next(state: &mut u64) -> u64 {
        *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut mixed = *state;
        mixed = (mixed ^ (mixed >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        mixed = (mixed ^ (mixed >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        mixed ^ (mixed >> 31)
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

    /// fz-kdt.119 REVERSES fz-kdt.104's headline on this pair, and the reason
    /// it may is that the premise changed under it.
    ///
    /// `{:cont, pair}` and `{:cont | :halt, pair}` used to be one question --
    /// both projected to "a 2-tuple" -- so offering both as arms would have let
    /// arm order, which is the scheduler's, decide whether `:halt` ever halts,
    /// and dropping the narrow twin was the only way to keep order out of the
    /// language. The tuple test now carries a sub-predicate per position, and
    /// position 0 is an ATOM: `{:cont}` and `{:cont, :halt}` are two questions,
    /// the plan can ask them, and the drop would now be throwing away a
    /// destination the runtime CAN route to.
    ///
    /// So the callsite compiles to an honest two-armed dispatch, and the seat
    /// is the wide arm first: the two overlap at the payload position, whose
    /// own test is blind to a nested list, and only the wide arm's surface
    /// names everything the narrow one's holds there. The old assertion and
    /// this one are the same law -- never let arm order decide meaning -- read
    /// against two different runtimes.
    #[test]
    fn a_narrower_twin_becomes_an_arm_once_the_test_can_tell_it_apart() {
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

        let CallDestinations::Dispatch(dispatch) =
            call_destinations(world.types_mut(), &summary).expect("destinations should compile")
        else {
            panic!("an atom position the plan can test makes the narrow twin a real destination");
        };
        assert_eq!(
            dispatch.targets,
            vec![target(command), target(cont)],
            "both arms survive, and the arm whose surface covers its sibling's blind payload \
             position is tested first",
        );
        let questions = runtime_questions(world.types_mut(), &dispatch.targets);
        assert_ne!(
            questions[0][1], questions[1][1],
            "the two arms put different questions to the state, which is what makes them two \
             destinations rather than a coin toss",
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
            dispatch.plan.matrix.arms.iter().all(|arm| arm
                .questions
                .iter()
                .any(|question| question.predicate.subject == SubjectId(1))),
            "every arm must ask which reducer arrived: {:#?}",
            dispatch.plan.matrix.arms,
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
            return_ty: None,
        };

        let questions = runtime_questions(world.types_mut(), &[target(boxed_one), target(boxed_other)]);
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

    /// The other half of the same law: the envelope preserves IDENTITY, never
    /// more.
    ///
    /// One callable closed over an `int` and the same callable closed over a
    /// `float` are one code pointer, and the capture record is not something a
    /// dispatch test reads back. So `{:tag, #66(int)}` and `{:tag, #66(float)}`
    /// are one question at every depth, exactly as they are at depth 0
    /// (fz-kdt.125), and the pair joins fz-kdt.127's population rather than
    /// getting a test that cannot be honoured.
    #[test]
    fn a_nested_callables_captures_are_not_a_question() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
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
            return_ty: None,
        };

        assert_ne!(boxed_int, boxed_float, "the lattice keeps the two capture types apart");
        let questions = runtime_questions(world.types_mut(), &[target(boxed_int), target(boxed_float)]);
        assert_eq!(
            questions[0], questions[1],
            "and the runtime cannot: one code pointer is one question, one tuple deep as at the top",
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
    /// NOWHERE erasing, `covers` holds both ways, and the second conjunct --
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
            return_ty: None,
        };
        let atoms_arm = target(atom_list, either);
        let ints_arm = target(int_list, all_one);

        let questions = runtime_questions(world.types_mut(), &[atoms_arm.clone(), ints_arm.clone()]);
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

    /// fz-kdt.107 step 3's trio, every arrival order: the head question seats
    /// the covering arm and leaves the rest exactly as they arrived.
    ///
    /// These are `enum_predicate_search`'s three `List.reduce_while_cont/3`
    /// arms, and they are the population whose native abort named this ticket:
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
    /// What the head buys is exactly one of the three pairs, and the law says
    /// which. B AND C OVERLAP AT THE HEAD (both admit an int) and differ only
    /// in a tail no test reads, so that pair is erasing and the seat must fall
    /// back to surface coverage -- which B has and C does not, so the seat
    /// moves B ahead of C. A against C is DISJOINT heads, a real separation,
    /// so no coverage is owed either way and neither arm is moved. A against B
    /// overlaps at `:true` and neither surface contains the other: no seat is
    /// escape-free, and arrival stands.
    ///
    /// The A/B pair is PINNED, not fixed. It is one of the two survivors of
    /// this ticket's escape census and it is fz-kdt.131's facet 3 -- overlap
    /// without containment -- whose cure is a repr-level or minting-level
    /// decision, not a seat.
    ///
    /// AND IT COSTS ONE SEAT, which is why all six orders are pinned rather
    /// than one law asserted. The correction is an insertion pass that stops
    /// at the first group it may not pass, because passing a group means
    /// passing everything between it and the destination. So on the ONE
    /// arrival that puts A between C and B -- `[C, A, B]` -- moving B ahead of
    /// C would also move it ahead of A, which is the pair the rule refuses to
    /// decide, and B stays where it arrived. That is not a gap in the head
    /// question: it is fz-kdt.131's residue standing in the way of this
    /// ticket's cure, measured rather than argued.
    #[test]
    fn a_list_head_seats_the_covering_arm_and_leaves_the_inseparable_pair_as_it_arrived() {
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

        // Arrival, and the seat it earns. Five of the six put B ahead of C,
        // which is the abort dying; the sixth is A standing between them.
        let expected = [
            (["A", "B", "C"], ["A", "B", "C"]),
            (["A", "C", "B"], ["A", "B", "C"]),
            (["B", "A", "C"], ["B", "A", "C"]),
            (["B", "C", "A"], ["B", "C", "A"]),
            (["C", "A", "B"], ["C", "A", "B"]),
            (["C", "B", "A"], ["B", "C", "A"]),
        ];
        let slot = |which: &str| match which {
            "A" => 0,
            "B" => 1,
            _ => 2,
        };
        for (arrived, wanted) in expected {
            let summary = CallSiteSummary {
                targets: arrived.iter().map(|which| arms[slot(which)].clone()).collect(),
                return_ty: None,
            };
            let CallDestinations::Dispatch(dispatch) =
                call_destinations(world.types_mut(), &summary).expect("destinations should compile")
            else {
                panic!("three arms over three element types are three destinations, arrived {arrived:?}");
            };
            let seated = dispatch.targets.iter().map(name).collect::<Vec<_>>();
            assert_eq!(
                seated, wanted,
                "the trio's seat moved on arrival {arrived:?}: B ahead of C wherever the pass can \
                 reach it, A and B exactly as they arrived, and no arm dropped",
            );
            let rank = |which: &str, order: &[&str]| order.iter().position(|arm| *arm == which);
            assert_eq!(
                rank("A", &seated) < rank("B", &seated),
                rank("A", &arrived) < rank("B", &arrived),
                "A and B overlap at `:true` and neither surface contains the other, so no seat is \
                 escape-free and arrival must stand (fz-kdt.131 facet 3) -- arrived {arrived:?}, \
                 seated {seated:?}",
            );
        }
    }

    /// The tail the head test cannot see, and the seat that answers for it.
    ///
    /// Two arms of ONE function, `[int]` and `[int | :ok]`, identical
    /// everywhere else. Their head questions OVERLAP -- both admit an int --
    /// and where they differ is the TAIL, which no test reads. So this pair is
    /// erasing however precisely the heads themselves are decided, and the
    /// only escape-free seat is the covering one: `[int | :ok]` first.
    ///
    /// THIS IS THE GATE THAT WOULD HAVE CAUGHT THE REFUTED RULE. Reading "the
    /// heads differ" as separation makes this pair separating, and the
    /// precision preference then seats the strictly-narrower `[int]` test
    /// first -- at which point `[1, :ok]` passes its head question and lands in
    /// the body that reads every element as an int. That is the abort this
    /// axis exists to kill, re-created by the axis meant to kill it.
    ///
    /// Both arms survive: a head question is what puts them in two groups, and
    /// `unroutable_alternatives` only drops within one. That is fz-kdt.118's
    /// drop lost, deliberately, and the native code it costs is fz-kdt.143's.
    #[test]
    fn an_arm_whose_head_overlaps_a_wider_one_is_seated_after_it() {
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
            let CallDestinations::Dispatch(dispatch) =
                call_destinations(world.types_mut(), &summary).expect("destinations should compile")
            else {
                panic!("two head questions are two destinations, and neither arm is dropped");
            };
            assert_eq!(
                dispatch.targets,
                vec![wide.clone(), narrow.clone()],
                "[int] and [int | :ok] agree at the head and disagree only in a tail no test \
                 reads, so the covering arm is seated first whichever way they arrived",
            );
        }
    }

    /// The carve-out fz-kdt.107 refuted a canonical order without: arms one
    /// runtime question cannot separate keep the order they arrived in.
    ///
    /// Two DIFFERENT functions taking the SAME lambda over different CAPTURES.
    /// A callable test reads the heap word at `+8`, which names the code a
    /// value was minted from and nothing about the environment beside it, so
    /// `#66 closed over an int` and `#66 closed over a float` are one and the
    /// same question. Nothing the plan emits tells the arms apart, and
    /// whichever is listed first receives every value the pair can see.
    /// Re-deciding that is not a reordering, it is a rerouting -- fz-kdt.107
    /// prototyped a canonical order over this class and got `{:done, 3}` where
    /// `{:halted, 3}` was due -- so the order is keyed on the GROUP: a key
    /// constant across a group cannot move a member of one.
    ///
    /// THE SHAPE HAS MOVED TWICE, and each move is a population leaving.
    /// It was two tagged tuples until fz-kdt.119 gave tuples a per-position
    /// test, which separates tags. It was `list(int)` against `list(:ok)`
    /// until fz-kdt.107 step 3 gave the list axis a head question, which
    /// separates disjoint element types. Same fn id, different captures, is
    /// what is left: fz-kdt.127's shape, the only genuinely inseparable
    /// population in the corpus, and the one this carve-out now exists for.
    #[test]
    fn runtime_indistinguishable_arms_keep_the_order_they_arrived_in() {
        let _tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let int = world.types_mut().int();
        let float = world.types_mut().float();
        let over_int = world.types_mut().closure_lit(ClosureTarget(66), vec![int], 1);
        let over_float = world.types_mut().closure_lit(ClosureTarget(66), vec![float], 1);
        let first_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "int_impl", 1);
        let second_fn = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "float_impl", 1);
        let target = |function, reducer| CallTargetSummary {
            callee: SelectedCallee::Function(function),
            surface_inputs: vec![reducer],
            activation: None,
            activation_inputs: None,
            return_ty: None,
        };
        let ints = target(first_fn, over_int);
        let atoms = target(second_fn, over_float);

        let questions = runtime_questions(world.types_mut(), &[ints.clone(), atoms.clone()]);
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

    /// fz-kdt.141, the instrument gate: a stress that cannot move an order
    /// proves nothing about it.
    ///
    /// Three arms on three DISTINCT questions, so `question_groups` gives three
    /// groups of one and the retired knob's within-group mirror is the
    /// IDENTITY -- and the questions are exact atoms that neither contain each
    /// other nor overlap on an erasing axis, so [`specificity_order`] declines
    /// to have an opinion and arrival order stands all the way through to the
    /// plan. That is the shape fz-kdt.131 owns and fz-kdt.107 step 3 leaves
    /// behind: entirely arrival-decided, and entirely invisible to a knob that
    /// only reverses groups.
    ///
    /// A seed moves it. That is the whole difference this ticket buys, and it
    /// is measured here rather than argued.
    #[test]
    fn a_seed_moves_an_arrival_order_the_group_reversal_cannot() {
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
            return_ty: None,
        };
        let arrived = vec![target(alpha), target(beta), target(gamma)];
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
}
