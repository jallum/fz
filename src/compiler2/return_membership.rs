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
//! member -- of a system of one when nothing else is on it. That is what
//! makes the return's owner known from an activation's first walk, before
//! any call site has a target, and what keeps an activation whose recursive
//! clause dispatch never reaches from waiting on a publisher that never
//! comes.
//!
//! The relation is symmetric and the component is its connected component, so
//! the answer does not depend on which member is asked -- the seed picks a
//! set, never a direction. That is what lets every member agree on one
//! canonical owner, which is the single publisher of all their return types.

use super::body::CallInputMode;
use super::identity::ActivationKey;
use super::semantic::{CallSiteKey, SemanticOrd as _};
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
/// this answer, and the component `seed` belongs to.
pub(crate) struct Discovery {
    pub(crate) frontier: Vec<ActivationKey>,
    pub(crate) component: Option<(Vec<ActivationKey>, ComponentUnknowns)>,
}

/// One "this call leaves its callee's return to a shared solve" edge.
struct UnsolvedCall {
    caller: ActivationKey,
    callee: ActivationKey,
    /// The callee slot the unsolved argument landed in, when the call names
    /// one. A call whose result alone is unsolved names none.
    slot: Option<usize>,
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
            let neighbour = match (edge.caller == member, edge.callee == member) {
                (true, _) => &edge.callee,
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
    for edge in &edges {
        if !members.contains(&edge.caller) || !members.contains(&edge.callee) {
            continue;
        }
        if edge.caller == edge.callee {
            self_edge = true;
        }
        if let Some(slot) = edge.slot
            && !slots.contains(&(edge.callee.clone(), slot))
        {
            slots.push((edge.callee.clone(), slot));
        }
    }
    // The frontier is every activation the relation mentions, member or not:
    // any of their call-site targets moving can redraw this boundary, so a
    // job that wants an attributable cause for its own membership has to
    // subscribe to all of them rather than only to the set it landed on.
    let mut frontier = members.clone();
    for edge in &edges {
        for key in [&edge.caller, &edge.callee] {
            if !frontier.contains(key) {
                frontier.push(key.clone());
            }
        }
    }
    // A function whose return is being solved owes it to a solve whatever
    // its call edges turn out to be. Dispatch can leave an activation with
    // none of them -- the clause that closes the cycle is unreachable for
    // this input -- and a system of one is still a system: the solve runs on
    // the branches that do reach and publishes their answer. Reading the
    // static answer here is what makes the owner known from the activation's
    // very first walk, before any call site has resolved a target.
    let owes = world
        .return_unknowns(seed.function)
        .is_some_and(|unknowns| unknowns.returns);
    let component = match owes || members.len() > 1 || self_edge {
        true => Some((members, ComponentUnknowns { slots })),
        false => None,
    };
    Discovery { frontier, component }
}

/// Every call, anywhere in this root, that hands its callee a value the
/// fixpoint is still solving.
///
/// The whole relation is built at once because membership is a connected
/// component of it, and a component is not a direction: a helper has to find
/// the caller that handed it the cycle just as surely as the caller has to
/// find the helper.
fn unsolved_calls(world: &World) -> Vec<UnsolvedCall> {
    let mut edges = Vec::new();
    let mut keys = world.activation_keys();
    keys.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    for caller in keys {
        let Some(unknowns) = world.return_unknowns(caller.function) else {
            continue;
        };
        let Some(analysis) = world.activation_analysis(&caller) else {
            continue;
        };
        for callsite in &analysis.callsites {
            let Some(site) = unknowns.callsite(*callsite) else {
                continue;
            };
            if site.is_settled() {
                continue;
            }
            let shapes = &site.arguments;
            let key = CallSiteKey {
                activation: caller.clone(),
                callsite: *callsite,
            };
            let Some(targets) = world.callsite_targets(&key) else {
                continue;
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
                        callee: callee.clone(),
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
                        callee: callee.clone(),
                        slot,
                    });
                }
            }
        }
    }
    edges
}
