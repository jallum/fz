//! Which activations solve their returns together.
//!
//! Keying is answered statically, before any activation exists
//! (`return_unknowns`). Membership is the same answer lifted to the
//! activations that actually exist: `wrap/1[a0]` and `nest/1[[int]]` solve one
//! system, while a second `nest/1[[binary]]` reached from elsewhere solves its
//! own, and only the call graph the analysis published says which is which.
//!
//! One rule draws every edge: a call is unsolved when it hands on an
//! argument the fixpoint is still solving, or when what it yields is itself
//! such a position. The argument case puts the callee's matching SLOT on the
//! caller's cycle -- that is how `wrap`, which mentions nothing recursive,
//! joins the cycle it is handed. The result case names no slot: a function
//! that wraps a constructor around its own recursive result hands on nothing
//! unsolved at all, and only its result says the two returns are one system.
//! Both halves of the rule are the STATIC answer, read from the caller's own
//! `FunctionUnknowns`; nothing here re-derives it, and nothing here decides a
//! key. That separation is what makes this settle: an answer that decided
//! keys would re-key the callee the moment it found one, the activation that
//! carried the evidence would vanish, and the discovery would undo itself
//! forever.
//!
//! Membership is not drawn from those edges alone. A function whose return
//! is being solved statically owes it to a solve whatever its activations'
//! call sites turn out to resolve to, so such an activation is always a
//! member -- of a system of one when nothing else is on it. A call site the
//! walk never reaches says nothing against that: the clause that closes the
//! cycle is unreachable for this input, and a system of one is the whole
//! answer, which is what keeps such an activation from waiting on a
//! publisher that never comes.
//!
//! A call site the walk REACHED and could not yet name a target for is the
//! other answer, and the two are not the same: that edge is UNKNOWN, not
//! absent, and whatever it turns out to reach may join the set. A
//! membership drawn across one is PARTIAL, and a partial membership is
//! nobody's to own and nothing to solve -- it is withheld until the site
//! names its targets. That is what keeps one return from being published
//! twice: once by the system the unknown edge hid, and again by the system
//! it turned out to be part of.
//!
//! The relation is symmetric and the component is its connected component, so
//! the answer does not depend on which member is asked -- the seed picks a
//! set, never a direction. That is what lets every member agree on one
//! canonical owner, which is the single publisher of all their return types.
//!
//! # Finding the component without scanning the world
//!
//! `discover` walks outward from `seed` in both directions at once, and
//! visits only activations the component actually reaches. The OUT
//! direction is the edge rule above, read one member at a time: for each of
//! a member's own unsettled call sites (`ReturnUnknowns(member.function)`),
//! its `CallSiteTargets` names the far end, when it has named one at all.
//!
//! The IN direction reads `Callers(member)` -- every call site that has ever
//! addressed `member`. `Callers` is cumulative: a site that once reached
//! `member` and later re-targets elsewhere is never withdrawn from it, so a
//! listed site is a CANDIDATE, not a fact on its own. What makes the
//! relation exact despite that is the same check the OUT direction already
//! makes, run from the other end: a candidate is a real edge only when its
//! own function's `ReturnUnknowns` still calls that site unsettled AND its
//! current `CallSiteTargets` still resolves to `member`. Both conditions are
//! read fresh, so a site that moved on answers `false` and is silently
//! skipped rather than trusted from a stale membership.
//!
//! Both directions run for every member the walk finds, whichever direction
//! found it, which is what keeps the two checks from disagreeing with each
//! other: an edge between two activations is drawn once from the caller's
//! side and once from the callee's `Callers` entry, and either walk reaches
//! the same neighbour. The cost of one query is proportional to the
//! component and its immediate callers, never to the size of the world.

use std::collections::HashSet;

use super::body::{CallInputMode, CallSiteId, callsite_input_modes};
use super::drive::FactKey;
use super::identity::ActivationKey;
use super::semantic::{CallSiteKey, CallSiteResolution};
use super::world::World;

/// The parameter slots one system solves for, in the order the walk found
/// them. A slot is one of these when a member hands it a value the fixpoint
/// is still solving; the solver seeds exactly these as its input unknowns.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ComponentUnknowns {
    slots: Vec<(ActivationKey, usize)>,
}

impl ComponentUnknowns {
    pub(crate) fn slots(&self) -> Vec<(ActivationKey, usize)> {
        self.slots.clone()
    }
}

/// What a membership query says about one activation.
///
/// Three answers rather than two: "in no system" and "not yet knowable" are
/// different facts and lead to different ownership, so they are one value
/// that says which it is.
pub(crate) enum Membership {
    /// Every call site out of this activation names its targets, and none
    /// leaves a return to a shared solve. The activation's own walk answers
    /// its return.
    Alone,
    /// A call site out of this activation has named no target yet. What it
    /// reaches may join a system, so whether this return is shared is still
    /// to be said and nobody may publish it meanwhile.
    Unknown,
    /// The activations this one solves its return with, and the positions
    /// that solve is over.
    Shared(Vec<ActivationKey>, ComponentUnknowns),
}

/// The result of one local walk: every activation that JOINED the
/// component (`members`), the slots found along the way, whether it met a
/// call site that has reached but not yet named a target (`unknown_edge`)
/// or a call that returns to an activation already on the walk
/// (`self_edge`), and every activation the walk TOUCHED regardless of
/// whether it joined (`visited`). `visited` is `members` plus the `Callers`
/// candidates `walk_in_edges` examined and ruled back out -- a stale entry
/// whose site has since moved on, or moved to name someone else. Those
/// reads happen whether or not the candidate turns out to be a member, so
/// they are part of what this walk cost, and `visited` is the count that
/// says so.
struct Walk {
    members: Vec<ActivationKey>,
    visited: Vec<ActivationKey>,
    slots: Vec<(ActivationKey, usize)>,
    unknown_edge: bool,
    self_edge: bool,
}

/// One local walk's whole answer: the membership it found, the component
/// members that answer is over, and how many activations the walk touched
/// reaching it. `reads_of` (below) turns `members` into the fact reads that
/// explain the boundary, but nothing here computes them eagerly -- a caller
/// that only wants the membership (five of the six call sites -- routing,
/// the frontier scan, the self-publish check) never pays for a read set it
/// never asks for. The one caller that needs both (the solve, which both
/// decides whether it still owns this component and subscribes to what
/// could redraw its boundary) asks `reads_of` itself, once, off the same
/// `members` this walk already found -- never a second walk.
pub(crate) struct Discovery {
    pub(crate) membership: Membership,
    pub(crate) members: Vec<ActivationKey>,
    pub(crate) visited: usize,
}

/// The connected component `seed` belongs to, discovered by a local
/// bidirectional walk rather than a scan of every activation this world
/// holds. Pure: no telemetry, so every caller -- routing, frontier scans,
/// the self-publish check, and the solve alike -- reads the one answer this
/// produces rather than choosing between two entry points.
pub(crate) fn discover(world: &World, seed: &ActivationKey) -> Discovery {
    let walk = walk(world, seed);
    let members = walk.members.clone();
    let visited = walk.visited.len();
    let membership = membership_of(world, seed, walk);
    Discovery {
        membership,
        members,
        visited,
    }
}

/// The fact reads that explain a discovered component's boundary: per
/// member, `CallSiteTargets` for each of its own unsettled sites (an
/// out-edge moving), `Callers` (an in-edge candidate arriving -- cumulative,
/// so it only grows), and `CallSiteTargets` for each unsettled site
/// `Callers` lists whose own activation is not itself a member (the check
/// that tells a candidate from a live edge; a member's own sites are already
/// covered by the first set). Built from `members` as the walk already found
/// them -- never a second walk -- so discovery and the solve's subscription
/// read the one relation this way and can never drift apart into separate
/// answers about the same boundary.
pub(crate) fn reads_of(world: &World, members: &[ActivationKey]) -> Vec<FactKey> {
    let member_set: HashSet<ActivationKey> = members.iter().cloned().collect();
    let mut reads = Vec::new();
    for member in members {
        for callsite in unsettled_out_sites(world, member) {
            reads.push(FactKey::CallSiteTargets(CallSiteKey {
                activation: member.clone(),
                callsite,
            }));
        }
        reads.push(FactKey::Callers(member.clone()));
        let Some(callers) = world.callers(member) else {
            continue;
        };
        for site in callers.sites() {
            if member_set.contains(&site.activation) {
                continue;
            }
            if is_unsettled_site(world, site) {
                reads.push(FactKey::CallSiteTargets(site.clone()));
            }
        }
    }
    dedup(reads)
}

/// One fact read once, in the order it was first reached.
fn dedup(reads: Vec<FactKey>) -> Vec<FactKey> {
    let mut seen = HashSet::new();
    reads.into_iter().filter(|fact| seen.insert(fact.clone())).collect()
}

fn membership_of(world: &World, seed: &ActivationKey, walk: Walk) -> Membership {
    // A function whose return is being solved owes it to a solve whatever
    // its call edges turn out to be. Dispatch can leave an activation with
    // none of them -- the clause that closes the cycle is unreachable for
    // this input -- and a system of one is still a system: the solve runs on
    // the branches that do reach and publishes their answer.
    let owes = world
        .return_unknowns(seed.function)
        .is_some_and(|unknowns| unknowns.returns);
    // That owed return is only answerable once every edge out of the set is
    // known. One unknown edge and the set could still grow, so the answer
    // says so rather than reporting the set as far as it goes: a partial
    // system that was published would have to be withdrawn when the edge
    // named what it reaches.
    match (walk.unknown_edge, owes || walk.members.len() > 1 || walk.self_edge) {
        (true, _) => Membership::Unknown,
        (false, true) => Membership::Shared(walk.members, ComponentUnknowns { slots: walk.slots }),
        (false, false) => Membership::Alone,
    }
}

/// One worklist walk from `seed`, both directions at once: every neighbour
/// found from either side is queued and, once dequeued, is itself asked for
/// its own out- and in-edges. That is what makes the answer a property of
/// the component rather than of the seed or of which direction reached a
/// member first.
fn walk(world: &World, seed: &ActivationKey) -> Walk {
    let mut members = vec![seed.clone()];
    let mut slots: Vec<(ActivationKey, usize)> = Vec::new();
    let mut unknown_edge = false;
    let mut self_edge = false;
    let mut rejected: Vec<ActivationKey> = Vec::new();
    let mut next = 0;
    while next < members.len() {
        let member = members[next].clone();
        next += 1;
        walk_out_edges(
            world,
            &member,
            &mut members,
            &mut slots,
            &mut unknown_edge,
            &mut self_edge,
        );
        walk_in_edges(world, &member, &mut members, &mut slots, &mut self_edge, &mut rejected);
    }
    let mut visited = members.clone();
    for candidate in rejected {
        if !visited.contains(&candidate) {
            visited.push(candidate);
        }
    }
    Walk {
        members,
        visited,
        slots,
        unknown_edge,
        self_edge,
    }
}

/// `activation`'s own static call sites, in stable position order. This is
/// the one place a `CallSiteId` is minted from a function's lowered body,
/// so it always carries the site's real span -- the span is part of a
/// `CallSiteId`'s identity, and a dynamic fact like `CallSiteTargets` is
/// keyed on the real one. (Reconstructing an id from `ReturnUnknowns`'
/// bare-`u32` domain instead, via `CallSiteId::from_u32`, mints
/// `Span::DUMMY` and so can never look up a fact published under the real
/// site -- the walk would find no edges at all.)
fn static_callsites(world: &World, activation: &ActivationKey) -> Vec<CallSiteId> {
    if !world.has_fact(&FactKey::LoweredBody(activation.function)) {
        return Vec::new();
    }
    let body = world.lowered_body(activation.function);
    let mut callsites: Vec<CallSiteId> = callsite_input_modes(&body).into_keys().collect();
    callsites.sort();
    callsites
}

/// Every call `member` itself makes that still owes its result or an
/// argument to a solve: for each of its own unsettled static call sites,
/// its current `CallSiteTargets` says whether the far end is unnamed
/// (`unknown_edge`) or named (an edge into whichever activation it names).
fn walk_out_edges(
    world: &World,
    member: &ActivationKey,
    members: &mut Vec<ActivationKey>,
    slots: &mut Vec<(ActivationKey, usize)>,
    unknown_edge: &mut bool,
    self_edge: &mut bool,
) {
    let Some(unknowns) = world.return_unknowns(member.function) else {
        return;
    };
    for callsite in static_callsites(world, member) {
        let Some(site) = unknowns.callsite(callsite) else {
            continue;
        };
        if site.is_settled() {
            continue;
        }
        let key = CallSiteKey {
            activation: member.clone(),
            callsite,
        };
        // Three answers, not two. No published targets at all is a call
        // site this walk does not reach, which is no edge; published-but-
        // unresolved is a call site it does reach whose far end is not yet
        // named.
        let targets = match world.callsite_target_resolution(&key) {
            None => continue,
            Some(CallSiteResolution::Unresolved) => {
                *unknown_edge = true;
                continue;
            }
            Some(CallSiteResolution::Resolved(targets)) => targets,
        };
        let shapes = &site.arguments;
        for target in &targets.targets {
            let Some(callee) = target.activation.clone() else {
                continue;
            };
            // A call site's positional arguments land at the END of a
            // closure callee's input space, behind its captures.
            let mode = match callee.input_len() == shapes.len() {
                true => CallInputMode::Direct,
                false => CallInputMode::Closure,
            };
            // The result edge names no slot: what this call yields is still
            // being solved, so the callee's whole return is on the caller's
            // cycle and nothing about the arguments says so.
            if site.result {
                record_edge(member, &callee, None, members, slots, self_edge);
            }
            for (index, shape) in shapes.iter().enumerate() {
                if shape.is_settled() {
                    continue;
                }
                let slot = mode.semantic_index(callee.input_len(), shapes.len(), index);
                record_edge(member, &callee, slot, members, slots, self_edge);
            }
        }
    }
}

/// Every call site `Callers(member)` lists that is still a live edge into
/// `member`: its own function's `ReturnUnknowns` still calls it unsettled,
/// and its current `CallSiteTargets` still resolves to `member`. `Callers`
/// is cumulative and never withdrawn, so most of the checking here is
/// ruling a stale candidate back OUT, not walking a new edge in. A
/// candidate ruled out is still recorded into `rejected`: the walk read its
/// facts to find out, so it is part of what this walk cost even though it
/// never joins `members`.
fn walk_in_edges(
    world: &World,
    member: &ActivationKey,
    members: &mut Vec<ActivationKey>,
    slots: &mut Vec<(ActivationKey, usize)>,
    self_edge: &mut bool,
    rejected: &mut Vec<ActivationKey>,
) {
    let Some(callers) = world.callers(member) else {
        return;
    };
    for site in callers.sites() {
        let Some(caller_site) = unsettled_site(world, site) else {
            if !rejected.contains(&site.activation) {
                rejected.push(site.activation.clone());
            }
            continue;
        };
        let names_member = matches!(
            world.callsite_target_resolution(site),
            Some(CallSiteResolution::Resolved(targets))
                if targets.targets.iter().any(|edge| edge.activation.as_ref() == Some(member))
        );
        if !names_member {
            if !rejected.contains(&site.activation) {
                rejected.push(site.activation.clone());
            }
            continue;
        }
        let shapes = &caller_site.arguments;
        let mode = match member.input_len() == shapes.len() {
            true => CallInputMode::Direct,
            false => CallInputMode::Closure,
        };
        if caller_site.result {
            record_edge(&site.activation, member, None, members, slots, self_edge);
        }
        for (index, shape) in shapes.iter().enumerate() {
            if shape.is_settled() {
                continue;
            }
            let slot = mode.semantic_index(member.input_len(), shapes.len(), index);
            record_edge(&site.activation, member, slot, members, slots, self_edge);
        }
    }
}

/// One "this call leaves its callee's return to a shared solve" edge: `to`
/// is the activation the slot belongs to, `from` is whoever hands it the
/// value. Either end may be new to the walk, so both are queued when they
/// are; a slot is recorded once, keyed by `to` and its index.
fn record_edge(
    from: &ActivationKey,
    to: &ActivationKey,
    slot: Option<usize>,
    members: &mut Vec<ActivationKey>,
    slots: &mut Vec<(ActivationKey, usize)>,
    self_edge: &mut bool,
) {
    if from == to {
        *self_edge = true;
    }
    for activation in [from, to] {
        if !members.contains(activation) {
            members.push(activation.clone());
        }
    }
    if let Some(slot) = slot {
        let key = (to.clone(), slot);
        if !slots.contains(&key) {
            slots.push(key);
        }
    }
}

/// Every call site `member`'s own function can make that is not yet
/// settled, in the function's stable position order.
fn unsettled_out_sites(world: &World, member: &ActivationKey) -> Vec<CallSiteId> {
    let Some(unknowns) = world.return_unknowns(member.function) else {
        return Vec::new();
    };
    static_callsites(world, member)
        .into_iter()
        .filter(|&callsite| unknowns.callsite(callsite).is_some_and(|site| !site.is_settled()))
        .collect()
}

/// `site`'s own `CallSiteUnknowns`, when its function still calls it
/// unsettled.
fn is_unsettled_site(world: &World, site: &CallSiteKey) -> bool {
    unsettled_site(world, site).is_some()
}

fn unsettled_site<'a>(world: &'a World, site: &CallSiteKey) -> Option<&'a super::return_unknowns::CallSiteUnknowns> {
    let unknowns = world.return_unknowns(site.activation.function)?;
    let site_unknowns = unknowns.callsite(site.callsite)?;
    (!site_unknowns.is_settled()).then_some(site_unknowns)
}

#[cfg(test)]
#[path = "return_membership_test.rs"]
mod return_membership_test;
