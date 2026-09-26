use std::borrow::Cow;
use std::cmp::Ordering;
use std::rc::Rc;

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
    pub(crate) plan: Rc<PatternDispatchPlan<Ty>>,
    pub(crate) targets: Vec<CallTargetSummary>,
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
    let arrived = arrival_order(types, &summary.targets);
    let surfaces = target_surfaces(&arrived);
    let (order, plan) = routable_alternatives(types, summary.arity(), &surfaces, &same_callee(&arrived))?;
    let targets = order.iter().map(|index| arrived[*index].clone()).collect::<Vec<_>>();
    let Some(plan) = plan else {
        return Ok(sole_destination(targets.into_iter().next()));
    };
    Ok(CallDestinations::Dispatch(Box::new(CallSiteDispatch {
        plan: Rc::new(plan),
        targets,
    })))
}

/// A callsite with no choice left to make.
fn sole_destination(target: Option<CallTargetSummary>) -> CallDestinations {
    match target {
        Some(target) => CallDestinations::Direct(target),
        None => CallDestinations::None,
    }
}

/// The routable alternatives among two or more -- which of them are
/// destinations at all, named by their arrival index and listed in the order
/// the plan tests them -- and the plan that tests them.
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
/// either: the drop, the seat and [`dispatch_columns`] read one and the same
/// reading of what the runtime can ask.
///
/// The plan is built here too, for the same reason: a caller that re-derived
/// the rows from a returned surface would be a second place deciding what the
/// plan asks and in what order. Both doors -- a callsite and a construction
/// wrapper -- get the same answer because there is only one place that gives
/// it. `None` where one alternative is left, which is a direct call at a
/// callsite and a single member at a wrapper.
fn routable_alternatives(
    types: &mut Types,
    arity: usize,
    surfaces: &[Vec<Ty>],
    same_callee: &dyn Fn(usize, usize) -> bool,
) -> Result<(Vec<usize>, Option<PatternDispatchPlan<Ty>>), PatternDispatchError> {
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
    let alternatives = permuted(routable, &order);
    if alternatives.len() <= 1 {
        return Ok((alternatives, None));
    }
    let observable = permuted(observable, &order);
    let questions = permuted(questions, &order);
    let columns = dispatch_columns(arity, &observable, &questions);
    let rows = observable
        .iter()
        .enumerate()
        .map(|(index, inputs)| dispatch_row(inputs, arity, &columns, index as PatternBodyId))
        .collect::<Vec<_>>();
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(arity, rows))?;
    Ok((alternatives, Some(plan)))
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
/// below. It costs nothing either, which [`dispatch_columns`] is what makes
/// true: the separating input leads, so a value is turned away at the first
/// question of every arm it walks through, whichever seat the pair was given.
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
/// It is a no-op in COST as well, and that half is [`dispatch_columns`]'s. A
/// plan asks a separating input before one the arms only overlap at, so a value
/// is turned away by the first question of every arm it walks through and a
/// selection costs one question per arm in EITHER seat. Before that rule the
/// seat was free of meaning but not of work -- put the arm with the covering
/// question first and the other arm's values answered it on the way past, three
/// matched questions where two were due, and this repair's choice between two
/// orders showed up in the surface-membership census. So the order this hands
/// out is a determinism choice and nothing else, which
/// `compiler2_no_value_reaches_a_construction_member_that_never_named_it` reads
/// back: flip `lex_elements_then_longer`'s tie-break, which is what decides
/// this order, and every census row stands where it stood.
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
/// The position verdict itself is [`separated_at`], which is also what
/// [`dispatch_columns`] folds the other way: two arms asking the identical
/// question at a position are not separated there, whatever that question
/// admits, and where EVERY arm asks it the plan drops the position and emits no
/// test at all.
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
    let separated = early_asks.len() != late_asks.len()
        || early_asks
            .iter()
            .zip(late_asks)
            .any(|(early, late)| separated_at(early, late));
    if separated {
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

/// Whether two arms' questions at ONE input admit no value in common, so the
/// plan's own test there keeps the two arms apart whichever way round they sit.
///
/// ONE RELATION, TWO READERS, exactly as [`seats_before`] is one relation for
/// the seat and the drop. [`seating`] folds it across the inputs to answer
/// whether a PAIR is separated at all; [`dispatch_columns`] folds it across the
/// pairs to answer whether an INPUT separates anything. Reading the same
/// verdict two ways is what lets the seat and the column order be one decision
/// made once.
///
/// ONE AND THE SAME QUESTION SEPARATES NOTHING, and this says so outright
/// rather than leaving `overlaps` to agree with itself. Two arms asking the
/// identical question at an input admit the identical set of values there,
/// whatever that set is. Asking `overlaps` there would make the answer turn on
/// a test being REALIZABLE, which not every one is: a tuple clause with a
/// subtracted signature loses its whole arity in
/// `runtime_type_predicate_tuple_arities`, so a surface holding every non-int
/// pair projects to a test that admits nothing and does not overlap ITSELF.
/// That is a defect in the projection and the projection's to cure; what it may
/// not do is decide a seat, a drop or a column order, and stated this way it
/// cannot -- `an_untested_position_is_not_a_separation` is the pair that proves
/// it.
fn separated_at(early: &RuntimeTypePredicate, late: &RuntimeTypePredicate) -> bool {
    early != late && !early.overlaps(late)
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
    pub(crate) plan: Option<Rc<PatternDispatchPlan<Ty>>>,
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
    let arity = edges.first().map_or(0, |edge| edge.surface.inputs.len());
    let surfaces = edges.iter().map(|edge| edge.surface.inputs.clone()).collect::<Vec<_>>();
    let (members, plan) = routable_alternatives(types, arity, &surfaces, &|_, _| true)?;
    Ok(ConstructionSelection {
        members,
        plan: plan.map(Rc::new),
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

/// The inputs the plan asks about, in the order it asks them -- Maranget's
/// column selection, decided from the very verdicts the seat reads.
///
/// # Which inputs
///
/// Only the ones the alternatives do not all carry ONE surface at. Where every
/// arm carries the same surface the emitted test would admit the same values to
/// every one of them, so it separates nothing and the plan does not ask it.
/// [`seating`] states the same fact from the other side: a subject the arms ask
/// identically is not a separation.
///
/// # In what order, and why the order is free to choose
///
/// A row is a CONJUNCTION over its inputs, and every row here lists the same
/// inputs, so listing them in another order leaves each arm admitting exactly
/// the set it admitted before. Arm order is untouched. A first-match walk over
/// unchanged arms admitting unchanged sets routes every value where it already
/// went: the column order decides how many questions a value answers on the
/// way, and nothing else. That is what makes this a free choice rather than a
/// routing one.
///
/// So spend it. A value bound for a later arm walks through the arms seated
/// ahead of it and leaves each one at the first question that refuses it. Ask a
/// SEPARATING input first -- one where some pair of arms admits no common value
/// -- and the value is turned away at that arm's first question. Ask an input
/// the arms only OVERLAP at first and the value answers it, is turned away by
/// the separating question behind it, and then answers its own arm's two: three
/// matched questions where two were due.
///
/// `List.reduce_while_step/3`'s `delivered_resume` continuation is the measured
/// case. Its two arms carry `{:cont | :halt, {[int], int}}` and `{:cont,
/// {[int], int}}` at one input -- one inside the other, so the tuple question
/// cannot turn either value away -- and two disjoint closure sets at another.
/// Asking the closure first costs two matched questions in EITHER seat, which
/// is also why the seat of a separated pair is a pure determinism choice
/// (see [`canonically_order_separated_neighbours`]).
///
/// Among inputs of one kind the plan keeps input order, which is a determinism
/// choice and nothing more.
fn dispatch_columns(arity: usize, observable: &[Vec<Ty>], questions: &[Vec<RuntimeTypePredicate>]) -> Vec<usize> {
    let Some(first) = observable.first() else {
        return Vec::new();
    };
    let (separating, overlapping): (Vec<usize>, Vec<usize>) = (0..arity)
        .filter(|input| observable.iter().skip(1).any(|inputs| inputs[*input] != first[*input]))
        .partition(|input| separates_some_pair(questions, *input));
    separating.into_iter().chain(overlapping).collect()
}

/// Whether the plan's own test at this input keeps some pair of arms apart.
fn separates_some_pair(questions: &[Vec<RuntimeTypePredicate>], input: usize) -> bool {
    questions.iter().enumerate().any(|(rank, early)| {
        questions[rank + 1..]
            .iter()
            .any(|late| separated_at(&early[input], &late[input]))
    })
}

fn dispatch_row(observable_inputs: &[Ty], arity: usize, columns: &[usize], body_id: PatternBodyId) -> PatternRow<Ty> {
    let mut patterns = Vec::with_capacity(arity);
    patterns.resize_with(arity, || Spanned::new(Pattern::Wildcard, Span::DUMMY));
    PatternRow {
        patterns,
        preconditions: columns
            .iter()
            .map(|input| (PatternSubjectRef::Input(*input as u32), observable_inputs[*input]))
            .collect(),
        guard: None,
        body_id,
    }
}

#[cfg(test)]
#[path = "callsite_dispatch_test.rs"]
mod callsite_dispatch_test;
