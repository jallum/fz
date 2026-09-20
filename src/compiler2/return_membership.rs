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

use super::body::{CallInputMode, CallSiteId, callsite_input_modes};
use super::drive::FactKey;
use super::identity::ActivationKey;
use super::semantic::{CallSiteKey, CallSiteResolution, SemanticOrd as _};
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

/// What one membership query found: every activation whose edges could redraw
/// this answer, and what it says about `seed`.
pub(crate) struct Discovery {
    pub(crate) frontier: Vec<ActivationKey>,
    pub(crate) membership: Membership,
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

/// One "this call leaves its callee's return to a shared solve" edge.
struct UnsolvedCall {
    caller: ActivationKey,
    end: CallEnd,
    /// The callee slot the unsolved argument landed in, when the call names
    /// one. A call whose result alone is unsolved names none, and so does an
    /// unknown end.
    slot: Option<usize>,
}

/// The far end of an unsolved call.
///
/// One of these two answers is a fact about the call graph and the other is
/// the absence of one, so they are one thing that says which it is rather
/// than two silences that look alike.
enum CallEnd {
    /// The activation this call hands its unsolved position to.
    Reaches(ActivationKey),
    /// The walk stood at this call site and could not name a target for it.
    /// What it reaches is still to be said, and until it is said no set
    /// drawn through this caller is complete.
    Unknown,
}

pub(crate) fn discover(world: &World, seed: &ActivationKey) -> Discovery {
    let edges = unsolved_calls(world);
    let mut members = vec![seed.clone()];
    let mut next = 0;
    // The relation is walked in both directions at once, which is what makes
    // the set a property of the seed's component rather than of the seed.
    while next < members.len() {
        let member = members[next].clone();
        next += 1;
        for edge in &edges {
            let CallEnd::Reaches(callee) = &edge.end else {
                continue;
            };
            let neighbour = match (edge.caller == member, *callee == member) {
                (true, _) => callee,
                (_, true) => &edge.caller,
                _ => continue,
            };
            if !members.contains(neighbour) {
                members.push(neighbour.clone());
            }
        }
    }
    let mut slots: Vec<(ActivationKey, usize)> = Vec::new();
    let mut self_edge = false;
    // An unknown edge out of a member is what makes this answer partial: the
    // member stood at a call and could not say what it reaches, so the set
    // drawn through it is a lower bound rather than an answer.
    let mut unknown_edge = false;
    for edge in &edges {
        if !members.contains(&edge.caller) {
            continue;
        }
        let CallEnd::Reaches(callee) = &edge.end else {
            unknown_edge = true;
            continue;
        };
        if !members.contains(callee) {
            continue;
        }
        if edge.caller == *callee {
            self_edge = true;
        }
        if let Some(slot) = edge.slot
            && !slots.contains(&(callee.clone(), slot))
        {
            slots.push((callee.clone(), slot));
        }
    }
    // The frontier is every activation the relation mentions, member or not:
    // any of their call-site targets moving can redraw this boundary, so a
    // job that wants an attributable cause for its own membership has to
    // subscribe to all of them rather than only to the set it landed on.
    let mut frontier = members.clone();
    for edge in &edges {
        let ends = match &edge.end {
            CallEnd::Reaches(callee) => vec![&edge.caller, callee],
            CallEnd::Unknown => vec![&edge.caller],
        };
        for key in ends {
            if !frontier.contains(key) {
                frontier.push(key.clone());
            }
        }
    }
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
    // system that was published -- by a solve over it, or by the walk of an
    // activation it had not yet reached -- would have to be withdrawn when
    // the edge named what it reaches.
    let membership = match (unknown_edge, owes || members.len() > 1 || self_edge) {
        (true, _) => Membership::Unknown,
        (false, true) => Membership::Shared(members, ComponentUnknowns { slots }),
        (false, false) => Membership::Alone,
    };
    Discovery { frontier, membership }
}

/// Every call, anywhere in this root, that hands its callee a value the
/// fixpoint is still solving.
///
/// The whole relation is built at once because membership is a connected
/// component of it, and a component is not a direction: a helper has to find
/// the caller that handed it the cycle just as surely as the caller has to
/// find the helper.
///
/// Each activation is asked about the call sites its function can make, not
/// about the ones its analysis has already resolved: the analysis names the
/// resolved sites alone, and a set drawn from those would read every site
/// still waiting on a target as a site that is not there.
fn unsolved_calls(world: &World) -> Vec<UnsolvedCall> {
    let mut edges = Vec::new();
    let mut keys = world.activation_keys();
    keys.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    for caller in keys {
        let Some(unknowns) = world.return_unknowns(caller.function) else {
            continue;
        };
        for callsite in static_callsites(world, &caller) {
            let Some(site) = unknowns.callsite(callsite) else {
                continue;
            };
            if site.is_settled() {
                continue;
            }
            let shapes = &site.arguments;
            let key = CallSiteKey {
                activation: caller.clone(),
                callsite,
            };
            // Three answers, not two. No published targets at all is a call
            // site this activation's walk does not reach, which is no edge;
            // published-but-unresolved is a call site it does reach whose
            // far end is not yet named.
            let targets = match world.callsite_target_resolution(&key) {
                None => continue,
                Some(CallSiteResolution::Unresolved) => {
                    edges.push(UnsolvedCall {
                        caller: caller.clone(),
                        end: CallEnd::Unknown,
                        slot: None,
                    });
                    continue;
                }
                Some(CallSiteResolution::Resolved(targets)) => targets,
            };
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
                // The result edge names no slot: what this call yields is
                // still being solved, so the callee's whole return is on the
                // caller's cycle and nothing about the arguments says so.
                if site.result {
                    edges.push(UnsolvedCall {
                        caller: caller.clone(),
                        end: CallEnd::Reaches(callee.clone()),
                        slot: None,
                    });
                }
                for (index, shape) in shapes.iter().enumerate() {
                    if shape.is_settled() {
                        continue;
                    }
                    let slot = mode.semantic_index(callee.input_len(), shapes.len(), index);
                    edges.push(UnsolvedCall {
                        caller: caller.clone(),
                        end: CallEnd::Reaches(callee.clone()),
                        slot,
                    });
                }
            }
        }
    }
    edges
}

/// Every call site this activation's function can make, in a stable order.
///
/// The set comes from the lowered body, so it is the same whichever
/// activation asks and however far any one walk has got; a function that is
/// not lowered yet can make no call anything here can see.
fn static_callsites(world: &World, activation: &ActivationKey) -> Vec<CallSiteId> {
    if !world.has_fact(&FactKey::LoweredBody(activation.function)) {
        return Vec::new();
    }
    let body = world.lowered_body(activation.function);
    let mut callsites: Vec<CallSiteId> = callsite_input_modes(&body).into_keys().collect();
    callsites.sort();
    callsites
}

#[cfg(test)]
#[path = "return_membership_test.rs"]
mod return_membership_test;
