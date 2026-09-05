use std::borrow::Cow;
use std::cmp::Ordering;

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
/// call can only offer as many destinations as the seat can put to use:
/// [`unroutable_alternatives`] names the arms the seat would never place ahead
/// of the arm that stands in for them, and dropping them here is what keeps
/// arm order out of the language's semantics.
///
/// What survives is then SEATED by [`specificity_order`], which corrects
/// arrival order wherever the arms themselves say it routes a value into a
/// body that never named it. The drop and the seat consult ONE relation --
/// [`seats_before`] -- read in two directions: the seat asks it of the pair it
/// is about to reorder, the drop asks it of an arm and its stand-in.
pub(crate) fn call_destinations(
    types: &mut Types,
    summary: &CallSiteSummary,
) -> Result<CallDestinations, PatternDispatchError> {
    if summary.targets.len() <= 1 {
        return Ok(sole_destination(summary.targets.first().cloned()));
    }
    let arity = summary.arity();
    let arrived = arrival_order(types, &summary.targets);
    let surfaces = target_surfaces(&arrived);
    let (order, observable_inputs) = routable_alternatives(types, &surfaces, &same_callee(&arrived));
    let targets = order.iter().map(|index| arrived[*index].clone()).collect::<Vec<_>>();
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

/// The routable alternatives among two or more: which of them are destinations
/// at all, named by their arrival index and listed in the order the plan tests
/// them, each paired with the widened surface its runtime questions are asked
/// about.
///
/// AN ALTERNATIVE IS A SURFACE AND A CALLEE, and nothing else. The drop and
/// the seat read a semantic surface per input and ask whether two alternatives
/// name one callee; whatever the caller hangs off that -- a
/// [`CallTargetSummary`] at a callsite, a [`CallableFlowEdge`] in a
/// construction wrapper's member list -- is the caller's business and it
/// re-associates by the index this returns. That is why there is ONE routing
/// rule and not one per plan kind (fz-kdt.179): member selection is a dispatch
/// like any other, and before this it was the one plan that ran neither the
/// drop nor the seat.
///
/// The projection runs ONCE here. Every alternative's observable surface and
/// the question that surface projects to are computed before the drop, the
/// survivors' are carried into the seat, and nothing downstream re-derives
/// either: the drop and the seat read one and the same reading of what the
/// runtime can ask.
fn routable_alternatives(
    types: &mut Types,
    surfaces: &[Vec<Ty>],
    same_callee: &dyn Fn(usize, usize) -> bool,
) -> (Vec<usize>, Vec<Vec<Ty>>) {
    let observable_inputs = observable_inputs(types, surfaces);
    let questions = runtime_questions(types, &observable_inputs);
    let unroutable = unroutable_alternatives(types, same_callee, &observable_inputs, &questions);
    let (routable, surviving): (Vec<_>, Vec<_>) = observable_inputs
        .into_iter()
        .zip(questions)
        .enumerate()
        .filter(|(index, _)| !unroutable.contains(index))
        .unzip();
    let (observable, questions): (Vec<_>, Vec<_>) = surviving.into_iter().unzip();
    let order = specificity_order(types, &questions, &observable);
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
/// Neither containment is the criterion on its own. SURFACE COVERAGE is, and
/// only for a pair that is a routing question at all: [`seating`] answers
/// `Covering` for `(early, late)` when some value satisfies BOTH groups' tests
/// and, at every position where their tests could both admit a value on an
/// ERASING axis (`overlaps_on_an_erasing_axis` -- list tails, tuple payloads,
/// struct/map/binary/resource contents), `early`'s surface already contains
/// `late`'s. "The tests differ" is NOT separation on those axes -- arities
/// {2} and {2,3} both admit a 2-tuple -- so difference alone never excuses
/// the surface check; only exact axes (ints, floats, atoms, callables) can,
/// because a value passes an exact test only by being in the tested set,
/// which the arm's surface names. Under that definition, seating a covering
/// arm first cannot escape anything, by construction.
///
/// A pair the plan's own tests keep apart OUTRIGHT -- no value satisfies both,
/// because at some position their questions are disjoint -- is neither
/// covering nor blind. It is `Seating::Separated`, no seat between them routes
/// anything either way, and the pair keeps arrival order (fz-kdt.186).
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
/// [`seats_before`] says so, which is the whole of this rule's opinion and is
/// also what [`unroutable_alternatives`] consults before it drops an arm.
///
/// THREE RESIDUES THE SEAT DOES NOT DECIDE, and each is a different fact. The
/// members of one question GROUP are inseparable -- a value reaches both, and
/// which of them receives it is what their order MEANS (fz-kdt.107). A pair
/// where neither group covers the other overlaps WITHOUT CONTAINMENT -- a
/// value reaches both, and their order decides which representation reads it
/// (fz-kdt.131). Both of those KEEP ARRIVAL ORDER, and must.
///
/// The third is a SEPARATED pair, and it is not like the other two: no value
/// reaches both arms, so neither order routes anything anywhere and the order
/// they arrived in was never a fact about the program. That one residue is
/// given a canonical order, by [`canonically_order_separated_neighbours`]
/// below.
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
/// under `Covering`, which admits no blind escape; every other pair sits
/// exactly as arrival left it. So the seat's blind escapes are a SUBSET of
/// arrival order's -- this rule can only ever remove them, never add one. The
/// `debug_assert` below holds every callsite of every debug compile to it,
/// which the fixture matrix drives across the corpus. Construction-wrapper
/// member selection runs this same seat now (fz-kdt.179), so the static census
/// that once read the property back off the landed artifact is retired.
///
/// `Covering` is not transitive (two groups can be blind at different
/// positions), so no rank or comparator linearizes it; that is why the pass is
/// an explicit insertion rather than a sort, and why a blocked move leaves
/// arrival order standing instead of forcing an order the arms do not
/// justify.
///
/// # The separated residue, and the one order it may be given
///
/// Of the three residues above, the SEPARATED pair is the only one whose order
/// carries no routing at all, and [`canonically_order_separated_neighbours`]
/// runs after the insertion pass to take that free axis away where it can: a
/// pair of ADJACENT groups no value can reach both of is put in
/// [`Types::cmp_activation_tys`] order of what the two say, so the artifact stops
/// recording which of them the fixpoint happened to settle first. Adjacency is
/// the whole safety argument and it is also the limit -- a run settles only
/// where it is pairwise separated end to end, and a non-separated pair of any
/// kind stops the repair there. fz-kdt.107's and fz-kdt.131's residues keep
/// arrival order, and must.
fn specificity_order(types: &Types, questions: &[Vec<RuntimeTypePredicate>], observable: &[Vec<Ty>]) -> Vec<usize> {
    let groups = grouped_by_question(questions);
    if groups.len() < 2 {
        return (0..questions.len()).collect();
    }
    let mut seated: Vec<usize> = Vec::with_capacity(groups.len());
    for group in 0..groups.len() {
        let mut at = seated.len();
        while at > 0 && seats_before(types, questions, observable, &groups[group], &groups[seated[at - 1]]) {
            at -= 1;
        }
        seated.insert(at, group);
    }
    // What the seat alone decided, kept for the assert below and for nothing
    // else -- a release build pays neither the copy nor the walk.
    let insertion_pass = cfg!(debug_assertions).then(|| seated.clone()).unwrap_or_default();
    canonically_order_separated_neighbours(types, questions, observable, &groups, &mut seated);
    debug_assert!(
        only_separated_pairs_moved(types, questions, observable, &groups, &insertion_pass, &seated),
        "the canonical repair reordered a pair a value can reach both of, so it decided a routing \
         the seat itself declined to decide",
    );
    debug_assert!(
        every_inversion_covers(types, questions, observable, &groups, &seated),
        "a seat moved a group ahead of one whose surface it does not cover, so a value the plan admits \
         now reaches a body arrival order would have kept it out of",
    );
    seated.into_iter().flat_map(|group| groups[group].clone()).collect()
}

/// Put every ADJACENT separated pair the seat left behind into one canonical
/// order, and touch nothing else.
///
/// # Why exactly this pair, and no other
///
/// Reordering two arms changes where a value lands only if that value
/// satisfies BOTH arms' tests: a plan is a first-match walk, so a value only
/// one arm admits reaches that arm wherever the other sits, and a value
/// neither admits reaches neither. [`Seating::Separated`] is the statement
/// that no such value exists -- some subject's two questions admit nothing in
/// common, and a row is a conjunction over its subjects. So swapping a
/// separated pair is a routing no-op, by construction, and the order they were
/// in was never a fact about the program: it was the order the semantic
/// fixpoint's agenda delivered them in.
///
/// The other two residues are NOT this: a question group's members and an
/// overlap-without-containment pair are both reached by a common value, so
/// their order decides which body that value runs (fz-kdt.107) and which
/// representation reads it (fz-kdt.131). Neither may be reordered here, and
/// the adjacency discipline below is what guarantees they are not.
///
/// # Adjacent transpositions only, and why that is the whole safety argument
///
/// This is a repair, not a sort. One swap of two ADJACENT entries changes the
/// relative order of exactly one pair -- the pair it swapped -- and leaves
/// every other pair's relative order alone. So by induction over the swaps,
/// the only pairs whose order this can change are separated ones, and the
/// seat's guarantee survives untouched: every inversion against arrival order
/// is still either `Covering` or `Separated`, never `Escaping`, which is what
/// the caller's `debug_assert` re-checks against the permutation that comes
/// out.
///
/// A comparison SORT would not have that property. Sorting a run by a
/// comparator moves entries past neighbours the comparator never examined, so
/// a group could cross a pair the relation refuses -- and `Separated` is not
/// transitive (`A|B` and `B|C` separated says nothing about `A|C`), so there
/// is no run to sort in the first place. Refusing to look past the immediate
/// neighbour is what keeps a non-transitive relation from being read as a
/// total one.
///
/// # What it removes, and what it leaves
///
/// ```text
///     A B C   pairwise separated end to end   ->  typed activation order, from any arrival
///     A B C   A|B, B|C separated, A|C not     ->  blocked at B; both A|C orders survive
/// ```
///
/// THE LIMIT, STATED EXACTLY: the repair settles a run only where the run is
/// pairwise separated END TO END. A single non-separated pair anywhere in the
/// run stops it there, and everything the block sits between stays a function
/// of the arrival. That blocking pair is not necessarily one of the two
/// meaning-bearing residues: a `Covering` pair -- one the seat ITSELF decided,
/// on a fact about the arms -- blocks the repair the same way, and
/// `a_covering_pair_blocks_the_repair_and_leaves_the_arrival_showing` builds a
/// callsite with no fz-kdt.107 group and no fz-kdt.131 pair in it where two
/// arrivals still render two orders. So the honest claim is the narrow one:
/// this removes the free axis exactly where the axis was free, and it does not
/// make the artifact a function of the arm SET.
///
/// # The key, and the other key it is not
///
/// A group is compared by the typed-activation-LEAST OBSERVABLE surface among its
/// members, never by whichever member arrived first -- the members' own order
/// is fz-kdt.107's residue and a key read off it would put the schedule back.
/// The key is a strict total order across groups: the typed activation relation is `Equal` only on
/// identical `Ty` slices, identical surfaces project to identical questions,
/// and one question is one group -- so two distinct groups can never tie.
///
/// TWO KEYS, AND THEY ARE DIFFERENT QUANTITIES. This repair orders semantic
/// destinations by the typed activation relation over the OBSERVABLE ENVELOPE
/// ([`observable_inputs`], which is what the plan's rows are built from).
/// `plan_callable_flows` orders independent callable surfaces by their full
/// inputs before resolving their edges. That earlier order schedules resolution;
/// it does not order wrapper destinations. This function alone drops and seats
/// the finished edges, so no concordance between the two quantities is assumed.
///
/// # The one separation this may be reading off a fiction (fz-kdt.202)
///
/// [`seating`] separates a pair where some position answers
/// `!(early == late || early.overlaps(late))`. That guard covers a position
/// where BOTH arms carry the same unrealizable surface. It does not cover two
/// arms carrying DIFFERENT surfaces at a position where one projects to a
/// predicate admitting nothing -- `runtime_type_predicate_tuple_arities` drops
/// a negated signature's whole arity, so `{any, any} & not({int, int})`
/// projects to a test that admits nothing and does not overlap ITSELF
/// (fz-kdt.202). Such a pair reads `Separated` on a fiction, and under
/// fz-kdt.186 that only meant "leave alone" while here it means "MAY REORDER".
///
/// It is still a routing no-op, one step further along: [`dispatch_row`]'s
/// preconditions are these very same [`observable_inputs`] `Ty`s, so an arm
/// whose projected test admits nothing emits a row NO VALUE CAN TAKE, and
/// moving an unreachable row past its neighbour changes no destination.
/// Adjacency does the rest -- the dead row's own motion is the whole of the
/// effect, because every other pair's order is preserved.
///
/// So no realizability conjunct is owed here, and the population is measured
/// rather than assumed: over all 604 corpus fixtures, classifying every
/// `Separated` verdict as a FICTION when every separating position is
/// self-blind on one side, the fictional population is **0** -- at the settled
/// arrival and under `arms:1`/`:3`/`:6` and `wrappers:1`/`:6` alike -- against
/// 172 to 214 real separation readings per setting. Curing the projection is
/// fz-kdt.202's, and tightening [`seating`] is fz-kdt.186's; neither is on
/// this rule's critical path while that count is zero.
fn canonically_order_separated_neighbours(
    types: &Types,
    questions: &[Vec<RuntimeTypePredicate>],
    observable: &[Vec<Ty>],
    groups: &[Vec<usize>],
    seated: &mut [usize],
) {
    let keys = groups
        .iter()
        .map(|group| canonical_key(types, observable, group))
        .collect::<Vec<_>>();
    let mut settling = true;
    while settling {
        settling = false;
        for at in 1..seated.len() {
            let (early, late) = (seated[at - 1], seated[at]);
            let separated = matches!(
                seating(types, questions, observable, &groups[early], &groups[late]),
                Seating::Separated,
            );
            if separated
                && types.cmp_activation_tys(&observable[keys[early]], &observable[keys[late]]) == Ordering::Greater
            {
                seated.swap(at - 1, at);
                settling = true;
            }
        }
    }
}

/// The member whose observable surface speaks for a whole group: the
/// typed-activation-least of them.
///
/// A group is a set of arms one question cannot separate, and their order
/// within it is fz-kdt.107's residue -- so a group's canonical name may not be
/// read off which member came first. The least surface is a function of the
/// group's contents alone. Ties among members are surfaces that are EQUAL, so
/// which of them the minimum picks cannot change a comparison.
fn canonical_key(types: &Types, observable: &[Vec<Ty>], group: &[usize]) -> usize {
    *group
        .iter()
        .min_by(|left, right| types.cmp_activation_tys(&observable[**left], &observable[**right]))
        .expect("a question group holds at least one arm")
}

/// Whether the canonical repair kept its promise: every pair whose relative
/// order it changed is a pair no value can reach both of.
///
/// This is the SAFETY CLAIM ITSELF, checked against the two permutations
/// rather than against the reasoning that produced them. A first-match walk
/// sends a value to the first arm that admits it, so reordering two arms can
/// only move a value that satisfies BOTH -- and `Separated` says there is no
/// such value. So a repair that moves nothing else changes no destination
/// anywhere, and this is what says it moved nothing else.
///
/// It is written as a quantification over pairs and not as a replay of the
/// swaps, because the claim is about the RESULT: had the repair been a sort,
/// or had a swap been taken on a stale reading, this is the assertion that
/// would fire. Held on every seated plan of every debug compile, which the
/// fixture matrix drives across the corpus.
fn only_separated_pairs_moved(
    types: &Types,
    questions: &[Vec<RuntimeTypePredicate>],
    observable: &[Vec<Ty>],
    groups: &[Vec<usize>],
    before: &[usize],
    after: &[usize],
) -> bool {
    let rank = |order: &[usize]| {
        let mut ranks = vec![0usize; groups.len()];
        for (at, group) in order.iter().enumerate() {
            ranks[*group] = at;
        }
        ranks
    };
    let (was, now) = (rank(before), rank(after));
    (0..groups.len()).all(|x| {
        (x + 1..groups.len()).all(|y| {
            (was[x] < was[y]) == (now[x] < now[y])
                || matches!(
                    seating(types, questions, observable, &groups[x], &groups[y]),
                    Seating::Separated,
                )
        })
    })
}

/// Whether the seat would put `x` ahead of `y`: the OBLIGATION first (only one
/// direction is escape-free, so take it), the PRECISION preference second
/// (both directions are escape-free, so hand a value both tests admit to the
/// arm that named it most precisely -- fz-kdt.129).
///
/// ```text
///     covering(x, y)  and  ( not covering(y, x)  or  test(x) strictly inside test(y) )
/// ```
///
/// The relation is antisymmetric: if both directions held, both would need
/// `Covering` both ways, so both would rest on strict mutual containment of
/// the tests -- which makes the tests equal, and equal tests are one group.
///
/// A SEPARATED pair is false both ways for free, because `Covering` is exactly
/// what [`seating`] refuses such a pair: no value satisfies both tests, so
/// there is no routing to prefer (fz-kdt.186). The seat leaves it where it
/// found it, and [`canonically_order_separated_neighbours`] then puts it in
/// the one order that says something about the arms rather than about the
/// schedule (fz-kdt.194).
///
/// Where NEITHER side covers the other the relation is false both ways: no
/// seat is escape-free and it declines to have an opinion. That is the
/// fz-kdt.107 inseparable class one rung wider, a standing hazard of arrival
/// order that predates any seating rule, and fz-kdt.131 owns it -- the cure is
/// a runtime test that can see what the body relies on (fz-kdt.119's tuple
/// tags, fz-kdt.107's list elements), not a cleverer sort.
///
/// ONE RELATION, TWO READERS. [`specificity_order`] applies it as an insertion
/// pass over question groups; [`unroutable_alternatives`] asks it of a single
/// pair, because an arm the seat would never put ahead of the arm that stands
/// in for it is not a destination at all (fz-kdt.143). The two callers pass
/// different slices -- groups and singletons -- and that difference is safe in
/// one direction only, which [`unroutable_alternatives`] states.
fn seats_before(
    types: &Types,
    questions: &[Vec<RuntimeTypePredicate>],
    observable: &[Vec<Ty>],
    x: &[usize],
    y: &[usize],
) -> bool {
    let covering = |early: &[usize], late: &[usize]| {
        matches!(seating(types, questions, observable, early, late), Seating::Covering)
    };
    covering(x, y) && (!covering(y, x) || strictly_inside(questions, x, y))
}

/// Whether the seat added no blind escape: no group it moved ahead of a group
/// that ARRIVED before it is ESCAPING against it -- either its surface covers
/// that group's, or the two are separated and the move routes nothing.
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
        seated[rank + 1..].iter().all(|late| {
            early < late
                || !matches!(
                    seating(types, questions, observable, &groups[*early], &groups[*late]),
                    Seating::Escaping,
                )
        })
    })
}

/// What one ordered pair of question groups asks of a seat.
///
/// THREE answers and not two, because "does not cover" and "is not a routing
/// question at all" are different facts and only one of them is an objection.
/// A `bool` collapsed them: the coverage check runs position by position under
/// an `all`, so a pair whose tests are DISJOINT at one position -- a pair no
/// value satisfies both halves of -- passed that position on the separation
/// arm and was then judged blind at another, and the seat was told it owed
/// coverage for a routing that routes nothing (fz-kdt.186).
///
/// ONE RELATION, EVERY READER. [`seats_before`] reads it in both directions
/// for the seat and for the drop, [`every_inversion_covers`] reads it to check
/// the permutation that came out, and `drive_test`'s census mirrors it off the
/// landed artifact. A pair is a seat question only where this says so.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Seating {
    /// No value satisfies both groups' tests, so no order between them routes
    /// anything: the plan's own tests already keep them apart, whichever way
    /// round they sit. The seat has nothing to decide, and because there is
    /// nothing to decide the pair may be put in a canonical order instead of
    /// the one the fixpoint happened to deliver -- the ONE pair class of which
    /// that is true (fz-kdt.194,
    /// [`canonically_order_separated_neighbours`]).
    Separated,
    /// Some value satisfies both, and wherever the tests cannot separate it
    /// `early`'s surface already names everything `late` holds. Seating
    /// `early` first cannot hand a value to a body that never named it.
    Covering,
    /// Some value satisfies both, and at some position the tests are blind
    /// while `late` holds values `early` does not name. Seating `early` first
    /// routes such a value into a body its representation does not fit.
    Escaping,
}

/// How the seat may treat `(early, late)`.
///
/// REACHABILITY FIRST. A plan row is a CONJUNCTION over its subjects -- one
/// refused subject refuses the row -- and the subjects are independent
/// arguments, so a pair of arms admits a common call exactly when EVERY
/// position admits a common value. [`RuntimeTypePredicate::overlaps`] is that
/// question at one position; where any position answers no, the plan's own
/// test separates the two arms outright and no seat between them can route
/// anything anywhere.
///
/// COVERAGE SECOND, and only then. Position by position: either the two groups
/// ask questions that SEPARATE them there, and the plan's own test is what
/// keeps `late`'s values out of `early`; or the test is blind, and `early`'s
/// surface must already contain every value `late`'s holds. A group is a set
/// of arms one question cannot separate, so the surface half is checked across
/// the whole product: whichever member arrival puts first receives the values,
/// and every member of `late` may arrive at it.
///
/// Surface containment is the one containment a seat may be reasoned from.
/// Containment of the TESTS is not it -- a test is a projection and it drops
/// what the body reads. Containment of the SURFACES alone is not it either --
/// a surface says nothing about which values the emitted test will actually
/// hand over.
///
/// ONE AND THE SAME QUESTION SEPARATES NOTHING, and the separation check says
/// so outright rather than leaving `overlaps` to agree with itself. Two arms
/// asking the identical question at a position admit the identical set of
/// values there, whatever that set is, so the position cannot tell them apart
/// -- and where every arm asks it, `discriminating_inputs` drops the position
/// and the plan never emits the test at all. Asking `overlaps` there would
/// make the answer turn on a test being REALIZABLE, which not every one is: a
/// tuple clause with a subtracted signature loses its whole arity in
/// projection (`runtime_type_predicate_tuple_arities` removes the negated
/// signature's arity outright), so a surface holding every non-int pair
/// projects to a test that admits nothing and does not overlap ITSELF. That is
/// a defect in the projection and the projection's to cure; what it may not do
/// is decide a seat or a drop, and stated this way it cannot --
/// `an_untested_position_is_not_a_separation` is the pair that proves it.
///
/// So a Separated pair always differs at the separating position, which makes
/// that position DISCRIMINATING and the plan's own test the thing that keeps
/// the two arms apart.
/// `a_separated_pair_of_tests_is_a_disjoint_pair_of_surfaces` holds the other
/// direction over a battery covering every axis: two surfaces that share a
/// value project to tests that overlap.
///
/// Two arities cannot describe one call, so a length mismatch is separation.
fn seating(
    types: &Types,
    questions: &[Vec<RuntimeTypePredicate>],
    observable: &[Vec<Ty>],
    early: &[usize],
    late: &[usize],
) -> Seating {
    let (early_asks, late_asks) = (&questions[early[0]], &questions[late[0]]);
    if early_asks.len() != late_asks.len()
        || !early_asks
            .iter()
            .zip(late_asks)
            .all(|(early, late)| early == late || early.overlaps(late))
    {
        return Seating::Separated;
    }
    let covering = (0..early_asks.len()).all(|position| {
        !early_asks[position].overlaps_on_an_erasing_axis(&late_asks[position])
            || late.iter().all(|late| {
                early
                    .iter()
                    .all(|early| types.is_subtype(&observable[*late][position], &observable[*early][position]))
            })
    });
    match covering {
        true => Seating::Covering,
        false => Seating::Escaping,
    }
}

/// Whether every value `narrow`'s group's test admits, `wide`'s admits too,
/// and not the other way about.
///
/// One group is one question, so a group's test is any member's.
fn strictly_inside(questions: &[Vec<RuntimeTypePredicate>], narrow: &[usize], wide: &[usize]) -> bool {
    test_inside(questions, narrow[0], wide[0]) && !test_inside(questions, wide[0], narrow[0])
}

/// Whether every value `narrow`'s test admits, `wide`'s admits too: input by
/// input, on the question the runtime is actually put.
///
/// This is the one spelling of test containment in this file. The seat asks it
/// of two groups through [`strictly_inside`]; the drop asks it of one pair, as
/// the conjunct of [`stands_in_for`] that surface containment does NOT imply.
fn test_inside(questions: &[Vec<RuntimeTypePredicate>], narrow: usize, wide: usize) -> bool {
    questions[narrow].len() == questions[wide].len()
        && questions[narrow]
            .iter()
            .zip(&questions[wide])
            .all(|(narrow, wide)| narrow.contained_in(wide))
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
/// observable domain that STRICTLY contains it, asking a question that admits
/// everything `narrow`'s question admits.
///
/// The same-callee conjunct is load-bearing: a multi-target callsite normally
/// names one target per SELECTED CALLEE -- that is what protocol dispatch is
/// (`jobs/semantic.rs` settles one `CallTargetSummary` per viable impl) -- and
/// a wider domain sitting on ANOTHER function's body is no stand-in at all.
///
/// Strictness is what makes the relation a strict partial order: it is
/// irreflexive and antisymmetric, both halves are transitive, and a maximal
/// element therefore has no stand-in and can never be dropped. Arms of equal
/// observable surface -- alike everywhere the runtime CAN look and different
/// only where it cannot -- are excluded by it and stay arrival-decided.
///
/// THE TEST CONJUNCT IS NOT IMPLIED BY THE SURFACE ONE, and the pair that
/// proves it is `[int | :ok] & not([:ok])` beside `[int | :ok]`. The narrow
/// type is the wide one with a clause carved out, so its SURFACE is strictly
/// inside -- but a negated list clause cannot be projected to a head question,
/// so its list axis degrades to `ListShapes::shape_only` and its TEST admits
/// `[:zzz]`, which its sibling's refuses. Drop it and `[:zzz]` stops escaping
/// into the narrow arm and starts reaching the wide arm's body or the plan's
/// fail node -- an outcome no arrival of those two arms ever produced, which
/// is precisely what the relative-soundness theorem forbids.
/// `a_narrow_surface_carrying_the_wider_test_is_not_dropped_for_it` pins it.
fn stands_in_for(
    types: &Types,
    same_callee: &dyn Fn(usize, usize) -> bool,
    observable: &[Vec<Ty>],
    questions: &[Vec<RuntimeTypePredicate>],
    wide: usize,
    narrow: usize,
) -> bool {
    same_callee(wide, narrow)
        && surface_inside(types, observable, narrow, wide)
        && !surface_inside(types, observable, wide, narrow)
        && test_inside(questions, narrow, wide)
}

/// Whether every value `narrow`'s observable surface holds, `wide`'s holds
/// too: input by input, on the surface the plan's rows are built from.
fn surface_inside(types: &Types, observable: &[Vec<Ty>], narrow: usize, wide: usize) -> bool {
    observable[narrow].len() == observable[wide].len()
        && observable[narrow]
            .iter()
            .zip(&observable[wide])
            .all(|(narrow, wide)| types.is_subtype(narrow, wide))
}

/// The partition of a callsite's targets by the question their observable
/// surfaces project to.
///
/// One group is one question: every member asks the runtime the same thing of
/// every input, so no emitted test separates them and whichever member the
/// graph reaches first receives every value the group can see.
///
/// It is a SEATING and STRESS concept, not the drop's. [`specificity_order`]
/// moves whole groups, because moving one member of a group past another would
/// re-decide a routing nothing the plan emits decides (fz-kdt.107), and
/// `dispatch_stress::reverse_indistinguishable_groups` mirrors each group to
/// reach exactly that arrival-kept residue. The drop quantifies over every
/// arm, one pair at a time, and never consults a group (fz-kdt.143).
///
/// Neither the observable surface nor the question is the settled semantic
/// surface. `runtime_type_test_envelope` erases what no runtime test can look
/// at -- a callable's arrow goes, its CONSTRUCTION stays, function and capture
/// types together, because the value's own heap word names the construction
/// wrapper it was minted from and a wrapper is one function at one capture
/// layout -- and `RuntimeTypePredicate` is coarser again: `{:cont, pair}` and
/// `{:cont | :halt, pair}` both project to "a 2-tuple".
pub(crate) fn question_groups(types: &mut Types, targets: &[CallTargetSummary]) -> Vec<Vec<usize>> {
    grouped_by_question(&target_questions(types, targets))
}

/// The question each target puts to the runtime, projected the way the plan
/// projects it: the observable surface first, that surface's predicate second.
///
/// [`routable_alternatives`] does not call this -- it holds the observable
/// surfaces already and passes them straight to [`runtime_questions`]. This is
/// the door for a caller that has only targets.
fn target_questions(types: &mut Types, targets: &[CallTargetSummary]) -> Vec<Vec<RuntimeTypePredicate>> {
    let observable = observable_inputs(types, &target_surfaces(targets));
    runtime_questions(types, &observable)
}

/// The semantic surface each target offers, which is all
/// [`routable_alternatives`] reads of a target.
fn target_surfaces(targets: &[CallTargetSummary]) -> Vec<Vec<Ty>> {
    targets.iter().map(|target| target.surface_inputs.clone()).collect()
}

/// Whether two of a callsite's targets sit on one callee -- the conjunct
/// [`stands_in_for`] asks of every alternative set, answered here off the
/// selected callee a callsite settled per viable impl.
fn same_callee(targets: &[CallTargetSummary]) -> impl Fn(usize, usize) -> bool + '_ {
    move |left, right| targets[left].callee == targets[right].callee
}

/// The grouping itself: one group per distinct question, in arrival order.
///
/// The ONE spelling of "one question = one group". [`question_groups`] projects
/// targets and calls it; [`specificity_order`] is handed questions already
/// projected by [`routable_alternatives`] and calls it directly, so no caller
/// re-derives a projection another caller already has.
fn grouped_by_question(questions: &[Vec<RuntimeTypePredicate>]) -> Vec<Vec<usize>> {
    let mut groups = Vec::new();
    let mut grouped = vec![false; questions.len()];
    for index in 0..questions.len() {
        if grouped[index] {
            continue;
        }
        let group = (index..questions.len())
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
fn runtime_questions(types: &mut Types, observable: &[Vec<Ty>]) -> Vec<Vec<RuntimeTypePredicate>> {
    observable
        .iter()
        .map(|inputs| {
            inputs
                .iter()
                .map(|ty| types.runtime_type_predicate(ty))
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Each alternative's inputs widened to the surface a runtime test can read
/// back off a value -- the same projection the plan's rows are built from.
fn observable_inputs(types: &mut Types, surfaces: &[Vec<Ty>]) -> Vec<Vec<Ty>> {
    surfaces
        .iter()
        .map(|inputs| runtime_dispatch_inputs(types, inputs))
        .collect()
}

/// Which of a construction wrapper's members are destinations at all, in the
/// order the wrapper tests them, and the plan that tests them.
///
/// THE WELD, RE-DERIVED. fz-kdt.108 established that a selection row's
/// `body_id` indexes the parallel member list and must increase
/// monotonically, so the two are welded. This carries the weld as DATA:
/// `members` names the surviving edges in seated order, transport builds the
/// member list by walking exactly that, and row `i`'s `body_id` is `i`
/// because member `i` was PUT there by the same walk. Nothing assumes the
/// edge list's own order survives, and nothing may reorder either list
/// afterwards.
pub(crate) struct ConstructionSelection {
    /// The surviving members, in the order the plan tests them, each named by
    /// its index in the edge list the selection was computed from.
    pub(crate) members: Vec<usize>,
    /// `None` where one member is left: a wrapper with one destination calls
    /// it, exactly as a callsite with one target is a `Direct` call.
    pub(crate) plan: Option<PatternDispatchPlan<Ty>>,
}

/// A construction wrapper's member selection, seated and dropped by the ONE
/// routing rule.
///
/// A wrapper's members are a runtime choice like any other: the value carries
/// its call arguments, the plan asks its questions, and whichever member the
/// graph reaches first receives it. So the same two obligations apply --
/// [`unroutable_alternatives`] removes a member the seat would never put ahead
/// of the member that stands in for it, and [`specificity_order`] corrects the
/// order wherever a member would otherwise take values its own surface never
/// named. Before fz-kdt.179 this plan ran neither: its rows were built
/// straight from the edge list, which is the fz-kdt.108 typed activation order, and
/// that is a CONTENT order, not a safety one.
///
/// EVERY MEMBER OF ONE WRAPPER IS ONE CALLEE, which is why the stand-in test's
/// same-callee conjunct is satisfied outright here. A construction wrapper is
/// one function at one capture layout: each edge is derived from the same local
/// producer and capture types, varying only the planned call surface. Two
/// members are therefore two specializations of one
/// body, never two bodies. That also settles the drop's one open residue in this
/// caller's favour: fz-kdt.143's group-dissolution reroute is meaning-bearing
/// only between DIFFERENT callees, and there are none to be had.
pub(crate) fn construction_member_selection(
    types: &mut Types,
    edges: &[CallableFlowEdge],
) -> Result<ConstructionSelection, PatternDispatchError> {
    if edges.len() <= 1 {
        return Ok(ConstructionSelection {
            members: (0..edges.len()).collect(),
            plan: None,
        });
    }
    let arity = edges[0].surface.inputs.len();
    let surfaces = edges.iter().map(|edge| edge.surface.inputs.clone()).collect::<Vec<_>>();
    let (members, observable_inputs) = routable_alternatives(types, &surfaces, &|_, _| true);
    if members.len() <= 1 {
        return Ok(ConstructionSelection { members, plan: None });
    }
    let discriminating_inputs = discriminating_inputs(arity, observable_inputs.iter().map(Vec::as_slice));
    let rows = observable_inputs
        .iter()
        .enumerate()
        .map(|(index, inputs)| dispatch_row(inputs, arity, &discriminating_inputs, index as PatternBodyId))
        .collect::<Vec<_>>();
    let plan = pattern_dispatch_from_source(SourcePatternRows {
        input_count: arity,
        rows,
    })?;
    Ok(ConstructionSelection {
        members,
        plan: Some(plan),
    })
}

/// The alternatives no runtime test could ever route to: each is an arm the
/// seat itself would never put ahead of the arm that stands in for it.
///
/// # The law
///
/// ```text
///     unroutable(N)  <=>  exists W != N :  stands_in_for(W, N)
///                                     and  not seats_before(N, W)
/// ```
///
/// [`stands_in_for`] proves W is the same callee on a strictly wider surface
/// whose test admits everything N's admits, so W's body is complete for every
/// value N could receive. What is left to decide is whether N is worth
/// offering anyway, and the seat already answers that: [`seats_before`] is the
/// one relation that says which of two arms belongs first. An arm the seat
/// would put ahead of its stand-in is a live specialization -- a value both
/// tests admit reaches the body that named it most precisely. An arm the seat
/// would NOT put first is one of two things, and neither is a destination: it
/// is DEAD, because W precedes it and admits everything it admits; or it is a
/// HAZARD, kept ahead of W by a refusal elsewhere in the insertion pass, which
/// is a blind escape a legal arrival can produce and the settled order cannot.
///
/// For a stand-in pair that is a routing question at all, `seating(W, N)` is
/// `Covering` unconditionally -- W's surface contains N's at every position --
/// so the condition reduces to
///
/// ```text
///     keep N  <=>  covering(N, W)  and  test(N) strictly inside test(W)
/// ```
///
/// A stand-in pair that is SEPARATED is dropped, and that is not a loss:
/// [`stands_in_for`] already demands `test_inside(N, W)`, so at the position
/// their questions do not meet N's own question admits NOTHING, which makes
/// N's row unreachable by construction. Dropping a row no value can take
/// changes no routing (fz-kdt.186). The position is one the plan actually
/// TESTS, because [`seating`] separates only where the two questions DIFFER
/// and two arms whose surfaces differ at a position make it discriminating --
/// so "N's row is unreachable" is a fact about the emitted graph and not only
/// about the projection.
///
/// # Why this is fz-kdt.118's theorem, generalized rather than replaced
///
/// Where the two arms ask ONE question -- 118's whole population -- their
/// tests are equal, `strictly_inside` is false, and N is dropped. That is
/// 118's rule, decided identically, and
/// `a_map_content_no_test_can_read_leaves_only_the_wider_arm` pins it on a map
/// pair the axis cannot see inside.
///
/// What the quantifier adds is everything 118 lost when the axes learned to
/// separate. 118 iterated inside one question group, and fz-kdt.119's tuple
/// positions, fz-kdt.125/127's callables and fz-kdt.107 step 3's list heads
/// each turned a same-callee contained pair into TWO questions -- so the
/// group-local drop reached zero corpus pairs. This existential ranges over
/// ALL arms, and the population it adds beyond 118's is exactly
/// `{N : some W stands in for N and not covering(N, W)}` -- and "not covering"
/// is by definition "seating N ahead of W is a blind escape", which is the
/// predicate the corpus census counts.
///
/// # Relative soundness, and the one shape it does not cover
///
/// Take the arrival [survivors in post-drop seated order, then the dropped
/// arms widest-first]. It is a permutation of the settled targets, so it is an
/// order the fixpoint could have delivered, and the seat reproduces its own
/// output: for any two arms adjacent in a seated order the later one refuses
/// to pass the earlier -- either it stopped there when it was inserted, or the
/// earlier one passed it and antisymmetry forbids the reverse -- so re-seating
/// the survivors in the order they were seated in is the identity, and the
/// dropped arms arriving afterwards cannot reach back into it. Each dropped N
/// is then inserted and cannot pass its stand-in W: passing it needs
/// `seats_before(N, W)`, which the drop condition says is false. So W precedes
/// N in that arrival and admits everything N admits, N receives nothing, and
/// the routing the plan performs after the drop is one that legal arrival
/// already produced. The claim is never that N was unreachable in the
/// abstract, only that its values already had a legal home in W.
///
/// # Where that argument stops: the drop can DISSOLVE A GROUP
///
/// Every step above assumes the survivors group the same way with the dropped
/// arm present and without it, and one shape breaks that assumption. The seat
/// moves whole question groups and coverage quantifies over the product, so a
/// GROUP is harder to cover than any one member -- which means an arm that
/// shares its question with a SURVIVOR is part of what pins that survivor
/// behind a wider arm. Drop it and the group dissolves: the survivor is judged
/// alone, coverage may now run its way, and the seat promotes it past the arm
/// that used to swallow its values. Every arrival of the un-dropped arms sends
/// those values to the wider arm; after the drop they reach the survivor's
/// body instead, and no arrival produced that.
///
/// It is not a blind escape -- `seats_before` demands `Covering` before it moves
/// anything, so the promoted arm's surface names everything it now receives,
/// and `every_inversion_covers` and the corpus escape census both stay put. It
/// is a routing this rule decides that arm order used to.
/// `a_drop_that_dissolves_a_question_group_reseats_the_survivor_it_pinned`
/// builds the smallest case, three arms wide, and pins it.
///
/// The precondition is exactly "a dropped arm shares its question with a
/// surviving one", and NO callsite on the corpus has one: swept over all 597
/// fixtures at this landing, the count is zero, which is why the corpus reads
/// 0 behaviour movers on both doors. The residue is fz-kdt.118's as much as
/// this rule's -- 118 dropped a member of a group, which dissolves one just
/// the same.
///
/// What it can and cannot mean: the re-routed values lie in BOTH surfaces,
/// the promoted survivor's and the wider arm's. When those two arms are
/// specializations of ONE callee the move is meaning-neutral by construction
/// -- either body is a valid specialization for a value its surface names --
/// and the post-drop seat is simply the more precise one. It is meaning-
/// bearing only when they are DIFFERENT callees, which means the semantic
/// layer offered two callees for one value at one callsite: an ambiguity no
/// seat can resolve honestly, and the dispatch layer is the wrong place to
/// try. fz-kdt.176 owns that invariant -- targets of different callees at one
/// callsite have disjoint observable surfaces, or the overlap is a diagnostic
/// -- and with it this residue reduces to a statement about precision.
///
/// # Two facts about the shape of the check
///
/// SINGLETONS AGAINST GROUPS. The drop asks `seats_before` of two single arms
/// while the seat asks it of two question groups. Coverage quantifies over the
/// product of the two groups, so covering a whole group implies covering any
/// one member: a group reading can only be FALSER than the singleton one. The
/// mismatch cannot drop an arm the seat would have put ahead of its stand-in.
/// Reading it group-wise could only turn `covering(W, N)` false, which turns
/// `seats_before(N, W)` into plain `covering(N, W)` -- and for the singleton
/// check to have refused while that holds, the two tests must be equal, which
/// puts N and W in ONE group where no seat separates them at all. What the
/// mismatch does NOT cover is the grouping the drop CHANGES, which is the
/// section above.
///
/// NO CASCADE, AND NEVER EMPTY. `stands_in_for` is a strict partial order, so
/// a maximal arm has no stand-in and survives; and because the existential
/// ranges over every arm rather than the survivors, an arm dropped only on
/// account of another dropped arm is dropped by that one's own stand-in too.
///
/// # The hazard this rule inherits
///
/// A drop to a SINGLE destination makes the callsite a `Direct` call, which
/// also removes the plan's fail node: a value outside every arm's observable
/// domain would have trapped and now routes to the survivor. That conversion
/// is `sole_destination`'s, it predates this rule (fz-kdt.104), and it is
/// fenced by the semantic analysis rather than by anything here -- but this
/// rule reaches it across the whole arm set where 118 reached it only within
/// one question group. Measured on the corpus at this landing: 51 call
/// dispatch sites before and 51 after, so no callsite collapsed to `Direct`
/// that was not one already.
///
/// # What is left alone
///
/// Arms with no stand-in between them -- neither surface contains the other,
/// or the narrower carries the wider test, or they are different functions
/// entirely -- are not touched: dropping either would lose a body nothing else
/// can supply. Those callsites stay order-decided, and the cure is a runtime
/// predicate that can tell them apart rather than a smaller plan (fz-kdt.107,
/// fz-kdt.131 facet 3).
fn unroutable_alternatives(
    types: &Types,
    same_callee: &dyn Fn(usize, usize) -> bool,
    observable: &[Vec<Ty>],
    questions: &[Vec<RuntimeTypePredicate>],
) -> Vec<usize> {
    (0..observable.len())
        .filter(|narrow| {
            (0..observable.len()).any(|wide| {
                wide != *narrow
                    && stands_in_for(types, same_callee, observable, questions, wide, *narrow)
                    && !seats_before(types, questions, observable, &[*narrow], &[wide])
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
/// deterministically -- a covering-proven inversion is a fact about the arms,
/// not about when they turned up, and a pair no value reaches both of is put
/// in typed activation order whichever way it arrived, wherever the run it sits in is
/// separated end to end (fz-kdt.194). So permuting arrival does not perturb
/// the seat's own decisions at all; what it perturbs is exactly the RESIDUE
/// nothing decides: the members of one question group, where arrival is the
/// one thing standing between the corpus and a wrong answer (fz-kdt.107);
/// every pair where neither group covers the other, where no seat is any safer
/// than the one it came with (fz-kdt.131); and the separated pairs the
/// canonical repair could not reach past a non-separated neighbour, which is
/// the limit of fz-kdt.194 rather than a class of its own.
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
/// - a callable value's CONSTRUCTION-WRAPPER member order: runtime demand plans
///   and resolves each surface independently, then
///   [`construction_member_selection`] drops and seats the finished edges into
///   the member list.
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
/// function of (seed, length) so a finding replays.
///
/// WHAT EACH SURFACE STILL MOVES. Re-measured at `ca23b676f` + fz-kdt.194 over
/// the 604-fixture corpus, by backend-dump comparand: an arm seed moves 0
/// fixtures' artifacts (22 before fz-kdt.194's canonical order over separated
/// pairs), `arms:reverse` moves 0 (a group mirror is the identity on singleton
/// groups, and every group on this corpus is one), and a wrapper seed moves 19.
/// The arm surface reads 0 ON THIS CORPUS, which is not the same as closed:
/// [`canonically_order_separated_neighbours`] settles a run only where the run
/// is pairwise separated end to end, and this corpus's movers all were. The
/// wrapper surface still reads 19, and the repair is not declining it -- the
/// repair fires on wrapper members (14 / 10 / 14 swaps under `wrappers:1` /
/// `:6` / `:reverse`, 0 at the settled arrival). Those 19 carry fz-kdt.107's
/// and fz-kdt.131's residue, which no canonical order may touch.
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

    /// A test-only permutation of resolved construction edges before semantic
    /// member selection. `finish_callable_flows` applies it to completed product
    /// answers; `construction_member_selection` may then drop and reseat those
    /// edges and alone defines the wrapper members and selection rows.
    pub(crate) fn perturbed_construction_edges(edges: Vec<CallableFlowEdge>) -> Vec<CallableFlowEdge> {
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
        let narrow_list = world.types_mut().difference(wide_list, ok_list);
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
        world.types_mut().name_callable(ClosureTarget(66), "boxed_one/1");
        world.types_mut().name_callable(ClosureTarget(68), "boxed_other/1");
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
            .name_callable(ClosureTarget(66), "capturing_callable/1");
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
        world.types_mut().name_callable(ClosureTarget(66), "multiply_by_two/2");
        world
            .types_mut()
            .name_callable(ClosureTarget(68), "multiply_by_three/2");
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
    /// `discriminating_inputs` drops a position where every arm carries the
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
            discriminating_inputs(2, observable.iter().map(Vec::as_slice)),
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
            boundary_input_demands: Box::new([]),
        };

        let edges = [edge(atom), edge(tuple)];
        let dispatch = construction_member_selection(world.types_mut(), &edges)
            .expect("callable flow dispatch should compile")
            .plan
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
        world.types_mut().name_callable(ClosureTarget(66), "closure_a/1");
        world.types_mut().name_callable(ClosureTarget(68), "closure_b/1");
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
}
