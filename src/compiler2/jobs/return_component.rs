//! Solves every member's `ReturnType` for one recursive-return component at
//! once. `World::return_membership` derives membership and the component's
//! canonical owner fresh from `ReturnUnknowns` and `CallSiteTargets`; this
//! job trusts a fresh recomputation of that same query every time it runs,
//! self-abdicating the moment it is no longer that owner. Unlike
//! `DeriveTypeDef`'s abdication (a `@type` equation's component never
//! reshapes once parsed, so it never needs to be woken again), a return
//! component's boundary genuinely moves as call targets resolve, so
//! abdication here still declares the read set the discovery's `reads`
//! hands back alongside the answer: the EDGE facts (never a forward-cone
//! node's whole `ActivationAnalyzed`) that could redraw the boundary the
//! same walk found it across. That subscription is what attributes the
//! abdication to a real cause and lets this job be re-woken if ownership
//! ever returns. An `Unknown` membership is a different exit entirely, not a
//! third kind of abdication: nobody owns the component yet, so this job
//! waits on the reached-but-Unresolved edges instead of concluding, and
//! every `ReturnType` it already published stays standing until they settle
//! (see `solve_return_component`'s own comment at that exit).
//!
//! # What the solve reads
//!
//! There is ONE lowering of "what does this function return": the static
//! `return_skeleton::Skeleton`, written in the function's own vocabulary
//! before any activation exists. This job evaluates that skeleton under one
//! activation's bindings, which are facts the walk already publishes:
//!
//! - a `Ground` value is what the activation's `value_types` observed at it;
//! - a `Result` is what the site's `CallSiteTargets` addressed, and, when a
//!   site addressed no activation at all, what the walk observed standing at
//!   the value it delivered;
//! - an `Input` slot is fed by the arguments its callers hand it, and by the
//!   input evidence already standing at that slot;
//! - which entries an activation returns through is its own
//!   `reachable_entries`.
//!
//! A [`Term`] is one of those bindings resolved, or a shape still to be read
//! in some activation's frame. Nothing here is a second tree language: the
//! only tree is the skeleton, and a term carries the address it is read at.
//!
//! # Guardedness
//!
//! A member's shape may reference another member (or itself) two ways:
//! *guarded*, nested inside a real constructor (`Tuple`, `List`, ...), or
//! *unguarded*, as a bare alternative of a union (or the whole top-level
//! shape). An unguarded reference carries no information of its own -- the
//! least fixed point of `x = x | y` is just `y` -- so [`Equations::build`]
//! reads the referent NODE's branches instead of descending into it, which
//! inlines every top-level unguarded reference away. A guarded reference is
//! left alone: it already denotes the standard regular/equi-recursive type
//! over however many times its cycle actually unfolds, which
//! `ComponentRef::Local` represents directly.
//!
//! # Three states, not two
//!
//! A position is in one of three states, and they are genuinely different:
//!
//! - *no branches at all*: no path reaches it, so there is nothing to say
//!   and nothing is published;
//! - *branches, none of which escape*: a productive cycle with no base case,
//!   whose least fixed point is the empty type, published as `none` -- a
//!   real, computed fact;
//! - *a branch resting on something nothing has observed yet*: the answer
//!   would be missing an alternative, so the position is PENDING and nothing
//!   is published until the observation arrives. An unknown is not `none`.
//!
//! An escaping, settled member's surviving branches lower to one
//! `DescrOf<ComponentRef>` each, folded by `union_regular_bodies`, and every
//! such member's body goes to `Types::intern_regular_bodies` in the same
//! call: the interner's own bisimulation partition refinement is what
//! collapses two members whose bodies turn out identical, so this job never
//! needs a separate closure-comparison step.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use crate::modules::identity::ModuleName;

use super::super::body::{CallInputMode, CallSiteId, ValueId};
use super::super::drive::{
    Derivation, DerivationKey, EvidenceSource, FactKey, Job, JobEffects, current_uses, settled_uses,
};
use super::super::identity::{ActivationKey, ActivationSignature, ModuleId};
use super::super::return_skeleton::{Returns, Skeleton};
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationInput, ActivationInputAlternatives, CallSiteKey, ProjectStep, SemanticOrd as _, join_contributions,
};
use super::super::types::{ComponentRef, DescrOf, MapKey, Ty, Types, union_regular_bodies};
use super::super::world::World;

/// One value the solve talks about: a binding already resolved, or a shape
/// still to be read in the frame of the activation named beside it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Term {
    /// No path reaches this position.
    Bottom,
    /// A position nothing has observed yet. Not the empty type: a node
    /// resting on one is not answerable at all.
    Unobserved,
    /// A type settled outside this system.
    Settled(Ty),
    /// What one activation hands back.
    Return(ActivationKey),
    /// What arrives at one member's parameter slot: an unknown of this
    /// system.
    Slot(ActivationKey, usize),
    /// The input evidence already standing at one activation's slot.
    Evidence(ActivationKey, usize),
    /// A shape read in one activation's own vocabulary. Its children are
    /// read in the same frame.
    Shape(ActivationKey, Skeleton),
}

/// What every leaf of every skeleton this solve reads resolves to, gathered
/// while the world is still readable. A binding is never derived here: each
/// one is a fact some other job already published, read at the address the
/// skeleton names.
#[derive(Debug, Default)]
struct Bindings {
    /// What each activation's walk observed standing at each of its values.
    value_types: HashMap<ActivationKey, HashMap<ValueId, Ty>>,
    /// What each call site yields: the activations it addressed, or -- when
    /// it addressed none at all -- what the walk observed standing at the
    /// value the call delivered.
    results: HashMap<(ActivationKey, CallSiteId), Vec<Term>>,
    /// Every member's return, one alternative per entry its activation
    /// actually reaches.
    returns: HashMap<ActivationKey, Vec<Term>>,
    /// Every member slot's equation.
    slots: HashMap<(ActivationKey, usize), Vec<Term>>,
    /// The input evidence already standing at a slot.
    evidence: HashMap<(ActivationKey, usize), ActivationInput>,
    /// The return type of an activation outside this component.
    externals: HashMap<ActivationKey, Ty>,
    /// The name a struct brand carries into its solved type.
    module_names: HashMap<ModuleId, ModuleName>,
}

impl Bindings {
    /// What the walk observed standing at one value, which is the whole
    /// answer for a ground leaf. Nothing observed is an unknown, never `any`
    /// and never `none`.
    fn observed(&self, activation: &ActivationKey, value: ValueId) -> Term {
        match self.value_types.get(activation).and_then(|types| types.get(&value)) {
            Some(ty) => Term::Settled(*ty),
            None => Term::Unobserved,
        }
    }
}

/// Either everything the solve needs, or the facts it is still missing.
enum Gathered {
    Ready(Box<Bindings>, Vec<(ActivationKey, usize)>),
    Waiting(Vec<FactKey>),
}

pub(super) fn solve_return_component(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    owner: &ActivationKey,
) -> Result<JobEffects, FatalError> {
    let discovery = world.return_membership(owner);
    let discovered_reads = discovery.reads(world);
    // One event per dispatch, by construction: `discovery` is this call's
    // one walk, and every exit below shares the same `discovered_reads` it
    // already found rather than asking a second walk for them.
    tel.dispatch(
        &["fz", "compiler2", "return_membership", "discovered"],
        &crate::measurements! { visited: discovery.visited(), members: discovery.members_len() },
        &crate::metadata! { seed: crate::telemetry::opaque(owner) },
    );
    // An `Unknown` membership is not a conclusion: some out-edge this walk
    // reached is still Unresolved, and what it turns out to reach may
    // enlarge the component, so nobody may publish this answer yet. Waiting
    // on these edges' own SETTLED movement (never their Current reading --
    // each already carries one, the Unresolved verdict itself, so a Current
    // wait would fire immediately with nothing new to say) is what keeps
    // this a blocked run rather than a wait-free one: `World::complete_job`
    // extends a blocked run's prior contributions instead of replacing them,
    // so every `ReturnType` this job already published for this component
    // stays standing until the edge resolves, rather than being retracted
    // and republished (or left unpublished) on every intervening revision.
    let unresolved = discovery.unresolved_out_edges();
    let Some(component) = discovery.into_component() else {
        return Ok(JobEffects {
            reads: current_uses(discovered_reads),
            waits: settled_uses(unresolved),
            ..JobEffects::default()
        });
    };
    if component.owner != *owner {
        // No longer the canonical owner -- some frontier activation's
        // analysis or call targets redrew the boundary since the last run.
        // Reading the frontier here (rather than concluding with an empty
        // read set) is what makes this abdication itself a caused event,
        // and what lets this job be woken again if ownership ever returns.
        return Ok(JobEffects {
            reads: current_uses(discovered_reads),
            ..JobEffects::default()
        });
    }
    let members = component.members;
    let member_set: HashSet<ActivationKey> = members.iter().cloned().collect();

    // `discovered_reads` names three kinds of fact: each member's own
    // unsettled out-edges, each member's `Callers` set (so a newcomer
    // joining the component wakes this solve), and the `CallSiteTargets` of
    // any non-member call site that already addresses a member. Any of
    // those moving can redraw the boundary this solve is trusting, so the
    // subscription is a real, attributable cause rather than an empty read
    // set standing in for one. It comes from the SAME walk that just
    // answered `component` above, not a second one.
    let mut reads: Vec<FactKey> = discovered_reads;
    let (bindings, slot_order) = match gather(world, &members, &member_set, &mut reads) {
        Gathered::Waiting(waits) => {
            return Ok(JobEffects {
                reads: current_uses(dedup(reads)),
                waits: current_uses(waits),
                ..JobEffects::default()
            });
        }
        Gathered::Ready(bindings, slot_order) => (bindings, slot_order),
    };

    let types = world.types_mut();
    let solved = solve(&members, &member_set, &bindings, &slot_order, types);

    let mut outputs = Vec::new();
    let mut changed = Vec::new();
    for member in &members {
        let fact = FactKey::ReturnType(member.clone());
        outputs.push(fact.clone());
        // Declared whatever the answer is: leaving the fact undeclared would
        // starve any waiter forever, since nothing else can ever settle it.
        // A member the solve could not answer -- no path reaches its return,
        // or a branch of it rests on something nothing has observed yet --
        // publishes no value, leaving whatever its own climb has reached
        // standing.
        let Some(evidence) = solved.returns.get(member).copied() else {
            continue;
        };
        let derivation = Derivation::of(
            Job::SolveReturnComponent(owner.clone()),
            DerivationKey::Activation(member.clone()),
        );
        if super::super::drive::ExecutionContext::new(world, tel).define_activation_return(&derivation, Some(evidence))
        {
            changed.push(fact);
        }
    }

    // The same solve settles each member's own INPUT evidence. A member's
    // slot equation is the join of every call site's argument shape, so its
    // solution is the closed form of an accumulator that would otherwise be
    // discovered one nesting at a time -- one rung per re-analysis, each rung
    // a fresh activation key. Contributing it back through the ordinary
    // contribution join lets the member's own walk see the settled shape
    // immediately: the argument it then passes to its recursive call is
    // already a fixed point, so the callee it mints is itself, and the ladder
    // never forms. `ActivationInputAlternatives::insert_row` drops the
    // standing rungs the settled row dominates.
    //
    // A row is one CORRELATED observation, so it exists only when the solve
    // named every column of it; a member whose slots the system did not all
    // reach contributes nothing here. Each column is the whole input the
    // solve settled -- type and callable surfaces alike -- so the row is one
    // the member's own walk could equally have published, and the ordinary
    // evidence join recognises it as the row already standing rather than
    // adding an alternative beside it.
    //
    // Contributed through the ordinary `activation_input_contributions`
    // field, the same one every other publisher uses: this job's own
    // `EvidenceSource` is `Settled` (`World::complete_job`, via
    // `evidence_source_for`), so its cell lands at the `Settled` edge and
    // nothing subscribes there. `gather` below reads the `Seed` cell and
    // each non-member `Call` cell for a member, never `Settled` and never a
    // member's own `Call` cell (already modeled structurally as a
    // `Term::Shape` binding) -- that is what keeps this solve from waking on
    // its own publish.
    let mut activation_input_contributions = Vec::new();
    for member in &members {
        let row: Option<Vec<ActivationInput>> = (0..member.input_len())
            .map(|slot| solved.slots.get(&(member.clone(), slot)).cloned())
            .collect();
        if let Some(row) = row {
            activation_input_contributions.push((member.clone(), row));
        }
    }

    tel.dispatch(
        &["fz", "compiler2", "return_component", "solved"],
        &crate::measurements! { member_count: members.len() as u64, bodies_supplied: solved.returns.len() as u64 },
        &crate::metadata! {
            world: crate::telemetry::opaque(&*world),
            activation: crate::telemetry::opaque(owner),
            members: crate::telemetry::opaque(&members),
        },
    );

    Ok(JobEffects {
        reads: current_uses(dedup(reads)),
        outputs,
        changed,
        activation_input_contributions,
        ..JobEffects::default()
    })
}

/// One fact read once, in the order it was first reached.
fn dedup(reads: Vec<FactKey>) -> Vec<FactKey> {
    let mut seen = HashSet::new();
    reads.into_iter().filter(|fact| seen.insert(fact.clone())).collect()
}

/// Reads every binding the members' skeletons name.
fn gather(
    world: &mut World,
    members: &[ActivationKey],
    member_set: &HashSet<ActivationKey>,
    reads: &mut Vec<FactKey>,
) -> Gathered {
    let mut bindings = Bindings::default();
    let mut waits = Vec::new();
    // Each frame is one activation and the shapes read in its vocabulary,
    // which is what the leaf walk below needs addresses for.
    let mut frames: Vec<(ActivationKey, Vec<Skeleton>)> = Vec::new();

    for member in members {
        // Not the whole analysis: only the part this solve reads out of it --
        // which entries the activation returns through, and the types
        // standing at its function's `Ground` leaves and its unaddressed
        // `Result` leaves (an addressed `Result` leaf is answered by the
        // component's own equations below, never by this read). A publisher
        // moving some other part of its analysis does not wake this solve.
        reads.push(FactKey::ReturnSolveInputs(member.clone()));
        reads.push(FactKey::ReturnSkeleton(member.function));
        let analysis = world.activation_analysis(member);
        let skeleton = world.return_skeleton(member.function);
        if analysis.is_none() {
            waits.push(FactKey::ReturnSolveInputs(member.clone()));
        }
        if skeleton.is_none() {
            waits.push(FactKey::ReturnSkeleton(member.function));
        }
        let (Some(analysis), Some(skeleton)) = (analysis, skeleton) else {
            continue;
        };
        // WHICH entries an activation returns through is a property of that
        // activation, so the static shapes are joined against its own
        // reachability rather than folded flat in the skeleton.
        let (shapes, terms) = match &skeleton.returns {
            Returns::Declared(ty) => (Vec::new(), vec![Term::Settled(*ty)]),
            Returns::Opaque => panic!("opaque provider return entered a compiler-owned return component"),
            Returns::Entries(entries) => {
                let shapes = analysis
                    .reachable_entries
                    .iter()
                    .filter_map(|entry| entries.get(entry).cloned())
                    .collect::<Vec<_>>();
                let terms = shapes
                    .iter()
                    .map(|shape| Term::Shape(member.clone(), shape.clone()))
                    .collect();
                (shapes, terms)
            }
        };
        bindings.returns.insert(member.clone(), terms);
        bindings
            .value_types
            .insert(member.clone(), analysis.value_types.clone());
        frames.push((member.clone(), shapes));
    }
    if !waits.is_empty() {
        return Gathered::Waiting(waits);
    }

    // A member's slot is fed by the arguments its callers hand it. A caller
    // that hands on a value the fixpoint is still solving is itself a member
    // -- that is exactly the edge `return_membership` draws -- so the callers
    // worth reading here are the members. Every other caller hands over a
    // settled value, which the walk already recorded in the slot's own input
    // evidence.
    for caller in members {
        let Some(skeleton) = world.return_skeleton(caller.function) else {
            continue;
        };
        // Every call site the function's own skeleton names, not just the
        // ones a walk has resolved so far: a still-unresolved site's
        // `CallSiteTargets` is read (and so subscribed) here directly, which
        // is what wakes this solve the moment it resolves, without needing
        // `ActivationAnalysis.callsites` to restate the same set.
        for (callsite, arguments) in &skeleton.arguments {
            let key = CallSiteKey {
                activation: caller.clone(),
                callsite: *callsite,
            };
            reads.push(FactKey::CallSiteTargets(key.clone()));
            let Some(targets) = world.callsite_targets(&key) else {
                continue;
            };
            for edge in &targets.targets {
                let Some(callee) = edge.activation.clone() else {
                    continue;
                };
                if !member_set.contains(&callee) {
                    continue;
                }
                // A call site's positional arguments land at the END of a
                // closure callee's input space, behind its captures.
                let mode = match callee.input_len() == arguments.len() {
                    true => CallInputMode::Direct,
                    false => CallInputMode::Closure,
                };
                for (index, argument) in arguments.iter().enumerate() {
                    let Some(slot) = mode.semantic_index(callee.input_len(), arguments.len(), index) else {
                        continue;
                    };
                    bindings
                        .slots
                        .entry((callee.clone(), slot))
                        .or_default()
                        .push(Term::Shape(caller.clone(), argument.clone()));
                }
                frames.push((caller.clone(), arguments.clone()));
            }
        }
    }

    // Membership is discovered, not declared: an activation minted after this
    // solve concludes can call a member and join the component. A member
    // gaining a caller is exactly what re-wakes this solve to rediscover
    // membership and answer for the newcomer too -- but that subscription is
    // already in `discovered_reads`, pushed once per member by
    // `return_membership::reads_of` from the same walk that found `members`
    // above. Reading it a second time here would name the same fact for the
    // same reason from two places, which is what `dedup` was papering over.

    // The evidence already standing at a member's slot is the base case of
    // its equation: a `Seed` cell is the member's own root/activation seed
    // (nonempty only for a closure's captured slots, which no call site's
    // arguments reach), and a `Call` cell is one caller's own contribution,
    // read only for callers OUTSIDE the component -- a member calling
    // itself or another member is never read here at all, because `gather`
    // already models that edge structurally, as the `Term::Shape` bindings
    // the loop above built from `CallSiteTargets`. Reading a member's own
    // `Call` cell too would represent that edge twice, the second copy a
    // function of the solve's own answer. The `Settled` cell -- this
    // solve's own row, from "The same solve settles each member's own INPUT
    // evidence" above -- is likewise never read: it is the edge nothing
    // subscribes to.
    let mut member_evidence: Vec<(ActivationKey, Vec<ActivationInputAlternatives>)> = Vec::new();
    for member in members {
        if member.input_len() == 0 {
            continue;
        }
        let mut cells: Vec<ActivationInputAlternatives> = Vec::new();
        reads.push(FactKey::ActivationCallEvidence {
            callee: member.clone(),
            from: EvidenceSource::Seed,
        });
        if let Some(seed) = world.activation_call_evidence(member, &EvidenceSource::Seed) {
            cells.push(seed.clone());
        }
        if let Some(callers) = world.callers(member) {
            for site in callers.sites() {
                if member_set.contains(&site.activation) {
                    continue;
                }
                let from = EvidenceSource::Call(site.activation.clone());
                reads.push(FactKey::ActivationCallEvidence {
                    callee: member.clone(),
                    from: from.clone(),
                });
                if let Some(cell) = world.activation_call_evidence(member, &from) {
                    cells.push(cell.clone());
                }
            }
        }
        if !cells.is_empty() {
            member_evidence.push((member.clone(), cells));
        }
    }
    let types = world.types_mut();
    for (member, cells) in member_evidence {
        let standing = join_contributions(types, cells.iter()).joined().to_vec();
        for (slot, input) in standing.into_iter().enumerate() {
            bindings.evidence.insert((member.clone(), slot), input);
            bindings
                .slots
                .entry((member.clone(), slot))
                .or_default()
                .insert(0, Term::Evidence(member.clone(), slot));
        }
    }

    let mut externals: Vec<ActivationKey> = Vec::new();
    let mut seen: HashSet<(ActivationKey, CallSiteId)> = HashSet::new();
    for (activation, shapes) in &frames {
        for shape in shapes {
            collect_leaves(
                world,
                activation,
                shape,
                member_set,
                &mut bindings,
                &mut seen,
                &mut externals,
                reads,
            );
        }
    }
    // Every activation the members name outside the component is a real data
    // dependency, but never a wait: exactly like an ordinary function call, a
    // still-absent external return is the ascent's bottom so far, not a
    // block, and the read alone is the subscription that re-wakes this solve
    // when the external's evidence rises. Waiting here would deadlock the
    // moment two components' owners depended on each other's members.
    externals.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    externals.dedup();
    for external in externals {
        reads.push(FactKey::ReturnType(external.clone()));
        if let Some(ty) = world.activation_return(&external) {
            bindings.externals.insert(external, ty);
        }
    }

    // A slot is an unknown of this system when what feeds it names a member.
    // A slot no member names is already settled by its callers, and seeding
    // it would restate their (arbitrarily wide) evidence for nothing.
    let mut slot_order = Vec::new();
    for member in members {
        for slot in 0..member.input_len() {
            let key = (member.clone(), slot);
            let Some(terms) = bindings.slots.get(&key) else {
                continue;
            };
            if terms.iter().any(|term| names_member(term, &bindings, member_set)) {
                slot_order.push(key);
            }
        }
    }
    Gathered::Ready(Box::new(bindings), slot_order)
}

/// Resolves every call site one shape reads through, and records the struct
/// names its brands will need.
#[allow(clippy::too_many_arguments)]
fn collect_leaves(
    world: &World,
    activation: &ActivationKey,
    shape: &Skeleton,
    member_set: &HashSet<ActivationKey>,
    bindings: &mut Bindings,
    seen: &mut HashSet<(ActivationKey, CallSiteId)>,
    externals: &mut Vec<ActivationKey>,
    reads: &mut Vec<FactKey>,
) {
    let recurse = |child: &Skeleton, bindings: &mut Bindings, seen: &mut _, externals: &mut _, reads: &mut _| {
        collect_leaves(world, activation, child, member_set, bindings, seen, externals, reads);
    };
    match shape {
        Skeleton::Bottom | Skeleton::Ground(_) | Skeleton::Input(_) => {}
        Skeleton::Result { callsite, value } => {
            if !seen.insert((activation.clone(), *callsite)) {
                return;
            }
            let key = CallSiteKey {
                activation: activation.clone(),
                callsite: *callsite,
            };
            reads.push(FactKey::CallSiteTargets(key.clone()));
            let addressed: Vec<ActivationKey> = world
                .callsite_targets(&key)
                .map(|targets| {
                    targets
                        .targets
                        .iter()
                        .filter_map(|edge| edge.activation.clone())
                        .collect()
                })
                .unwrap_or_default();
            // A call that addressed no activation -- a boundary edge, or a
            // target nothing has resolved yet -- denotes exactly what the
            // walk saw standing at the value it delivered.
            let terms = match addressed.is_empty() {
                true => vec![bindings.observed(activation, *value)],
                false => addressed.into_iter().map(Term::Return).collect(),
            };
            for term in &terms {
                if let Term::Return(key) = term
                    && !member_set.contains(key)
                {
                    externals.push(key.clone());
                }
            }
            bindings.results.insert((activation.clone(), *callsite), terms);
        }
        Skeleton::Union(branches) | Skeleton::Tuple(branches) => {
            for branch in branches {
                recurse(branch, bindings, seen, externals, reads);
            }
        }
        Skeleton::List { element, .. } => recurse(element, bindings, seen, externals, reads),
        Skeleton::Map(fields) => {
            for (_, value) in fields {
                recurse(value, bindings, seen, externals, reads);
            }
        }
        Skeleton::Struct(module, fields) => {
            if let Some(name) = world.module_name(*module) {
                bindings.module_names.insert(*module, name.clone());
            }
            for (_, value) in fields {
                recurse(value, bindings, seen, externals, reads);
            }
        }
        Skeleton::Project { of, .. } => recurse(of, bindings, seen, externals, reads),
    }
}

/// Whether a term reaches any activation in `members`, as a whole return or
/// as one of their parameter slots. This is what makes a slot an unknown of
/// the component's system rather than a value its callers have settled.
fn names_member(term: &Term, bindings: &Bindings, members: &HashSet<ActivationKey>) -> bool {
    match term {
        Term::Bottom | Term::Unobserved | Term::Settled(_) | Term::Evidence(_, _) => false,
        Term::Return(key) => members.contains(key),
        Term::Slot(activation, _) => members.contains(activation),
        Term::Shape(activation, shape) => names_member_shape(activation, shape, bindings, members),
    }
}

fn names_member_shape(
    activation: &ActivationKey,
    shape: &Skeleton,
    bindings: &Bindings,
    members: &HashSet<ActivationKey>,
) -> bool {
    let names = |child: &Skeleton| names_member_shape(activation, child, bindings, members);
    match shape {
        Skeleton::Bottom | Skeleton::Ground(_) => false,
        Skeleton::Input(_) => members.contains(activation),
        Skeleton::Result { callsite, .. } => bindings
            .results
            .get(&(activation.clone(), *callsite))
            .is_some_and(|terms| terms.iter().any(|term| names_member(term, bindings, members))),
        Skeleton::Union(branches) | Skeleton::Tuple(branches) => branches.iter().any(names),
        Skeleton::List { element, .. } => names(element),
        Skeleton::Map(fields) | Skeleton::Struct(_, fields) => fields.iter().any(|(_, value)| names(value)),
        Skeleton::Project { of, .. } => names(of),
    }
}

/// One unknown of the component's equation system. A member's whole return
/// and a member's parameter slot are the unknowns the component is named
/// for. An auxiliary unknown stands for every other position that needs a
/// node of its own: a constructor's child, and a projection read back out of
/// a value whose own shape is still symbolic. Auxiliary unknowns are keyed
/// by the term itself, so the same position met twice along two paths is one
/// node -- which is what makes unfolding a projection around a cycle
/// terminate at the cycle instead of climbing it one rung at a time.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Unknown {
    Return(ActivationKey),
    Slot(ActivationKey, usize),
    Aux(Term),
}

/// The equation system: one node per [`Unknown`], each carrying the
/// flattened branches its own value is the union of. Every reference a
/// branch makes at a structural-child position is itself a node here, so the
/// whole system is a finite graph over subterms of the members' skeletons,
/// ready to hand to `Types::intern_regular_bodies` in one call.
struct Equations<'a> {
    members: &'a HashSet<ActivationKey>,
    bindings: &'a Bindings,
    index: HashMap<Unknown, usize>,
    nodes: Vec<Unknown>,
    branches: Vec<Vec<Term>>,
}

impl<'a> Equations<'a> {
    fn new(members: &'a HashSet<ActivationKey>, bindings: &'a Bindings) -> Self {
        Self {
            members,
            bindings,
            index: HashMap::new(),
            nodes: Vec::new(),
            branches: Vec::new(),
        }
    }

    fn node(&mut self, unknown: Unknown) -> usize {
        if let Some(&existing) = self.index.get(&unknown) {
            return existing;
        }
        let index = self.nodes.len();
        self.index.insert(unknown.clone(), index);
        self.nodes.push(unknown);
        self.branches.push(Vec::new());
        index
    }

    /// Reads a term's leaf against the bindings, so that everything past
    /// this point is either a value, a reference into this system, or a
    /// constructor. A skeleton says WHERE to look; a binding says what is
    /// there. Nothing observed at a leaf is an unknown, which is neither
    /// `any` nor `none`.
    fn bind(&self, term: &Term) -> Term {
        match term {
            Term::Shape(_, Skeleton::Bottom) => Term::Bottom,
            Term::Shape(activation, Skeleton::Ground(value)) => self.bindings.observed(activation, *value),
            Term::Shape(activation, Skeleton::Input(slot)) => self.slot_term(activation, *slot),
            Term::Slot(activation, slot) => self.slot_term(activation, *slot),
            Term::Shape(activation, Skeleton::Result { callsite, .. }) => {
                match self.bindings.results.get(&(activation.clone(), *callsite)) {
                    // One target is the ordinary case: the call site IS that
                    // activation's return, with no node of its own between.
                    Some(targets) if targets.len() == 1 => self.bind(&targets[0]),
                    Some(_) => term.clone(),
                    None => Term::Unobserved,
                }
            }
            Term::Return(key) if !self.members.contains(key) => match self.bindings.externals.get(key) {
                Some(ty) => Term::Settled(*ty),
                None => Term::Unobserved,
            },
            other => other.clone(),
        }
    }

    /// A slot inside the component is an unknown the solve answers; a slot
    /// outside it is whatever evidence already stands there.
    fn slot_term(&self, activation: &ActivationKey, slot: usize) -> Term {
        match self.members.contains(activation) {
            true => Term::Slot(activation.clone(), slot),
            false => match self.bindings.evidence.contains_key(&(activation.clone(), slot)) {
                true => Term::Evidence(activation.clone(), slot),
                false => Term::Unobserved,
            },
        }
    }

    /// The equation a node's value is defined by: a member's own return
    /// shapes, a slot's joined argument shapes, or the auxiliary term the
    /// node stands for.
    fn equation(&self, unknown: &Unknown) -> Vec<Term> {
        match unknown {
            Unknown::Return(key) => self.bindings.returns.get(key).cloned().unwrap_or_default(),
            Unknown::Slot(key, slot) => self
                .bindings
                .slots
                .get(&(key.clone(), *slot))
                .cloned()
                .unwrap_or_default(),
            Unknown::Aux(term) => vec![term.clone()],
        }
    }

    /// Solves every node's branch set as the least fixed point of one pass
    /// over the node vector, repeated until nothing moves.
    ///
    /// A node's branches are what its equation denotes once every unguarded
    /// reference in it has been replaced by what that reference denotes. The
    /// node memo IS the termination argument: an unguarded reference reads
    /// the referent NODE's current branches rather than descending into its
    /// equation, so a cycle of unguarded references simply reads a partial
    /// answer this round and a larger one next, converging on the least fixed
    /// point instead of unfolding forever. Recomputing a node from scratch
    /// each round keeps every branch set a function of its inputs alone, so
    /// the whole system is deterministic; branch sets only ever grow, over a
    /// finite universe of subterms, so the rounds are finite.
    fn build(&mut self, seeds: Vec<Unknown>, types: &mut Types) {
        for seed in seeds {
            self.node(seed);
        }
        loop {
            let mut moved = false;
            let mut next = 0;
            while next < self.nodes.len() {
                let unknown = self.nodes[next].clone();
                let computed = self.expand_node(&unknown, types);
                // Merged, never replaced: a branch set only ever grows, and
                // keeping the order it grew in is what makes the whole system
                // a function of the members' skeletons rather than of the
                // round a branch happened to arrive in.
                let standing: HashSet<&Term> = self.branches[next].iter().collect();
                let arrived: Vec<Term> = computed
                    .into_iter()
                    .filter(|branch| !standing.contains(branch))
                    .collect();
                if !arrived.is_empty() {
                    self.branches[next].extend(arrived);
                    moved = true;
                }
                // Every structural child of a surviving branch is itself a
                // node of this system, so the lowering walk never has to mint
                // one: it only resolves.
                let children: Vec<Unknown> = self.branches[next]
                    .clone()
                    .iter()
                    .flat_map(|branch| self.branch_children(branch))
                    .filter_map(|child| self.child_unknown(&child))
                    .collect();
                for child in children {
                    self.node(child);
                }
                next += 1;
            }
            if !moved {
                break;
            }
        }
    }

    /// One node's branch set, recomputed from its equation and the memo.
    fn expand_node(&mut self, unknown: &Unknown, types: &mut Types) -> Vec<Term> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        if let Unknown::Aux(Term::Shape(activation, Skeleton::Project { of, step })) = unknown {
            // A projection reads one layer out of whatever its subject
            // denotes. Its subject's branches are already constructors or
            // leaves, so reading through them is a step DOWN into subterms,
            // never a further unfolding of the cycle the subject sits on.
            let mut inner = Vec::new();
            let mut inner_seen = HashSet::new();
            self.expand_into(
                &Term::Shape(activation.clone(), (**of).clone()),
                &mut inner,
                &mut inner_seen,
            );
            for branch in inner {
                let projected = self.project_branch(&branch, step, types);
                self.expand_into(&projected, &mut out, &mut seen);
            }
            return out;
        }
        for term in self.equation(unknown) {
            self.expand_into(&term, &mut out, &mut seen);
        }
        out
    }

    /// Adds what `term` denotes to `out`: a constructor or a value is itself
    /// a branch, a union contributes each alternative, and an unguarded
    /// reference contributes its referent node's current branches.
    fn expand_into(&mut self, term: &Term, out: &mut Vec<Term>, seen: &mut HashSet<Term>) {
        let term = self.bind(term);
        match &term {
            Term::Bottom => {}
            Term::Return(key) => {
                let node = self.node(Unknown::Return(key.clone()));
                self.absorb(node, out, seen);
            }
            Term::Slot(activation, slot) => {
                let node = self.node(Unknown::Slot(activation.clone(), *slot));
                self.absorb(node, out, seen);
            }
            Term::Shape(activation, shape) => match shape {
                Skeleton::Union(alternatives) => {
                    for alternative in alternatives.clone() {
                        self.expand_into(&Term::Shape(activation.clone(), alternative), out, seen);
                    }
                }
                Skeleton::Result { callsite, .. } => {
                    let targets = self
                        .bindings
                        .results
                        .get(&(activation.clone(), *callsite))
                        .cloned()
                        .unwrap_or_default();
                    for target in targets {
                        self.expand_into(&target, out, seen);
                    }
                }
                Skeleton::Project { .. } => {
                    let node = self.node(Unknown::Aux(term.clone()));
                    self.absorb(node, out, seen);
                }
                _ => {
                    if seen.insert(term.clone()) {
                        out.push(term.clone());
                    }
                }
            },
            _ => {
                if seen.insert(term.clone()) {
                    out.push(term.clone());
                }
            }
        }
    }

    fn absorb(&self, node: usize, out: &mut Vec<Term>, seen: &mut HashSet<Term>) {
        for branch in &self.branches[node] {
            if seen.insert(branch.clone()) {
                out.push(branch.clone());
            }
        }
    }

    /// Reads one layer out of a single already-flattened branch. Every
    /// in-component reference has been inlined by the time a branch reaches
    /// here, so a surviving reference names something outside the component
    /// and carries its own concrete type; a constructor hands back the
    /// companion it already holds at that position; a branch built from a
    /// different constructor promises no such layer at all, which is the
    /// empty type. A subject nothing has observed keeps the projection
    /// unknown rather than answering for it.
    fn project_branch(&self, branch: &Term, step: &ProjectStep, types: &mut Types) -> Term {
        match branch {
            Term::Bottom => Term::Bottom,
            Term::Unobserved => Term::Unobserved,
            Term::Settled(ty) => project_concrete(*ty, step, types),
            Term::Evidence(activation, slot) => match self.bindings.evidence.get(&(activation.clone(), *slot)) {
                Some(input) => project_concrete(input.ty(), step, types),
                None => Term::Unobserved,
            },
            Term::Return(_) | Term::Slot(_, _) => Term::Bottom,
            Term::Shape(activation, shape) => {
                let of = |child: &Skeleton| Term::Shape(activation.clone(), child.clone());
                match (shape, step) {
                    (Skeleton::Tuple(elements), ProjectStep::TupleField(index)) => {
                        elements.get(*index).map(of).unwrap_or(Term::Bottom)
                    }
                    (Skeleton::List { element, .. }, ProjectStep::ListElement) => of(element),
                    (Skeleton::List { element, .. }, ProjectStep::ListTail) => of(&Skeleton::List {
                        element: element.clone(),
                        non_empty: false,
                    }),
                    // A key the companion does not carry is exactly the case
                    // the observed type answers `any` for, and the two views
                    // have to agree.
                    (Skeleton::Map(fields) | Skeleton::Struct(_, fields), ProjectStep::MapField(wanted)) => fields
                        .iter()
                        .find(|(key, _)| key == wanted)
                        .map(|(_, value)| of(value))
                        .unwrap_or_else(|| Term::Settled(types.any())),
                    _ => Term::Bottom,
                }
            }
        }
    }

    /// The structural-child positions of one flattened branch: the positions
    /// that lower to a `ComponentRef` rather than to a descriptor of their
    /// own. Each one is handed back bound, so callers never re-read leaves.
    fn branch_children(&self, branch: &Term) -> Vec<Term> {
        let Term::Shape(activation, shape) = branch else {
            return Vec::new();
        };
        let children: Vec<Skeleton> = match shape {
            Skeleton::Tuple(elements) => elements.clone(),
            Skeleton::List { element, .. } => vec![(**element).clone()],
            Skeleton::Map(fields) | Skeleton::Struct(_, fields) => {
                fields.iter().map(|(_, value)| value.clone()).collect()
            }
            _ => Vec::new(),
        };
        children
            .into_iter()
            .map(|child| self.bind(&Term::Shape(activation.clone(), child)))
            .collect()
    }

    /// The node a structural child needs, if any. A value and a reference to
    /// something outside the component both carry their own answer already;
    /// everything else -- an in-component reference, a nested union, a
    /// nested constructor, a surviving projection -- is an equation node.
    fn child_unknown(&self, child: &Term) -> Option<Unknown> {
        match child {
            Term::Bottom | Term::Unobserved | Term::Settled(_) | Term::Evidence(_, _) => None,
            Term::Return(key) => Some(Unknown::Return(key.clone())),
            Term::Slot(activation, slot) => Some(Unknown::Slot(activation.clone(), *slot)),
            Term::Shape(_, _) => Some(Unknown::Aux(child.clone())),
        }
    }

    /// The least fixed point of "this node reaches a value": a node escapes
    /// once one of its branches does, and a branch escapes once every
    /// structural child position it fills escapes. A node with branches that
    /// never escapes is a productive cycle with no base case -- its value is
    /// the empty type. A node with no branches at all has no evidence yet,
    /// which is a different state entirely.
    fn escapes(&self) -> Vec<bool> {
        self.least_fixed_point(|equations, branch, reached| equations.branch_escapes(branch, reached))
    }

    /// The least fixed point of "this node is still waiting on something
    /// nothing has observed". A branch resting on an unobserved leaf has no
    /// answer yet -- as distinct from a branch no value reaches, which
    /// answers the empty type -- so the member holding it publishes nothing
    /// and keeps whatever its own climb has already reached.
    fn pending(&self) -> Vec<bool> {
        self.least_fixed_point(|equations, branch, reached| equations.branch_pending(branch, reached))
    }

    fn least_fixed_point(&self, holds: impl Fn(&Self, &Term, &[bool]) -> bool) -> Vec<bool> {
        let mut reached = vec![false; self.nodes.len()];
        loop {
            let mut advanced = false;
            for node in 0..self.nodes.len() {
                if reached[node] {
                    continue;
                }
                if self.branches[node].iter().any(|branch| holds(self, branch, &reached)) {
                    reached[node] = true;
                    advanced = true;
                }
            }
            if !advanced {
                break;
            }
        }
        reached
    }

    /// Whether a flattened branch -- a whole body in its own right -- reaches
    /// a value. Mirrors [`Solver::lower_branch`] arm for arm: a bare
    /// reference cannot become a whole descriptor (a `DescrOf` carries
    /// structure, never a raw reference), so only a reference already
    /// resolved to a concrete value escapes here.
    fn branch_escapes(&self, branch: &Term, escapes: &[bool]) -> bool {
        match branch {
            Term::Bottom | Term::Unobserved => false,
            Term::Settled(_) | Term::Evidence(_, _) => true,
            Term::Return(_) | Term::Slot(_, _) => false,
            Term::Shape(activation, shape) => match shape {
                Skeleton::Union(alternatives) => alternatives.iter().any(|alternative| {
                    self.branch_escapes(&Term::Shape(activation.clone(), alternative.clone()), escapes)
                }),
                Skeleton::Tuple(_) | Skeleton::List { .. } | Skeleton::Map(_) | Skeleton::Struct(_, _) => self
                    .branch_children(branch)
                    .iter()
                    .all(|child| self.child_escapes(child, escapes)),
                _ => false,
            },
        }
    }

    /// Whether a branch is still waiting on an unobserved leaf.
    fn branch_pending(&self, branch: &Term, pending: &[bool]) -> bool {
        match branch {
            Term::Unobserved => true,
            Term::Bottom | Term::Settled(_) | Term::Evidence(_, _) => false,
            Term::Shape(_, _) => self
                .branch_children(branch)
                .iter()
                .any(|child| self.child_pending(child, pending)),
            other => self.at_node(other, pending),
        }
    }

    /// Whether a structural-child position escapes. Unlike a whole-body
    /// position, a reference here is a normal recursive edge (it lowers to a
    /// `ComponentRef`, not a `DescrOf`), so it escapes exactly when the node
    /// it names does. Mirrors [`Solver::child_ref`].
    fn child_escapes(&self, child: &Term, escapes: &[bool]) -> bool {
        match child {
            Term::Bottom | Term::Unobserved => false,
            Term::Settled(_) | Term::Evidence(_, _) => true,
            other => self.at_node(other, escapes),
        }
    }

    fn child_pending(&self, child: &Term, pending: &[bool]) -> bool {
        match child {
            Term::Unobserved => true,
            Term::Bottom | Term::Settled(_) | Term::Evidence(_, _) => false,
            other => self.at_node(other, pending),
        }
    }

    /// What a flag says about the node a reference names, or `false` when
    /// the reference reaches no node of this system at all.
    fn at_node(&self, term: &Term, flags: &[bool]) -> bool {
        match self.child_unknown(term).and_then(|unknown| self.index.get(&unknown)) {
            Some(&node) => flags[node],
            None => false,
        }
    }
}

/// The callable surfaces a solved slot carries: the observations standing
/// behind every non-member parameter that reaches it. Only a leaf naming a
/// caller's parameter carries surfaces at all -- a value a constructor built
/// is not itself callable, and a `ReturnType` records no surfaces -- and a
/// member's own slot is inlined before a branch set is flattened, so the
/// flattened branches answer this directly. The surfaces are contributed in
/// the caller's frame, exactly as the walk contributes them; the evidence
/// join addresses them at the member's own slot on the way in.
fn slot_surfaces(branches: &[Term], bindings: &Bindings) -> BTreeSet<ActivationSignature> {
    branches
        .iter()
        .filter_map(|branch| match branch {
            Term::Evidence(activation, slot) => bindings.evidence.get(&(activation.clone(), *slot)),
            _ => None,
        })
        .flat_map(|input| input.callable_surfaces().iter().cloned())
        .collect()
}

/// Reads one layer out of a branch that already carries its own concrete
/// type. A type that promises no such layer is not an unconstrained value --
/// it is a branch of a different constructor, and no value of it ever
/// reaches this position -- so it contributes the empty type. Asking the
/// calculator for the layer anyway answers `any`, which is how one base
/// clause's `int` used to poison a whole system through a head read.
fn project_concrete(ty: Ty, step: &ProjectStep, types: &mut Types) -> Term {
    let carries_the_layer = match step {
        ProjectStep::ListElement | ProjectStep::ListTail => types.has_list_shape(&ty),
        ProjectStep::TupleField(index) => types.max_tuple_arity(&ty) > *index,
        // A key the type does not promise is exactly the case the ordinary
        // walk answers `any` for, and the two views have to agree.
        ProjectStep::MapField(_) => true,
    };
    match carries_the_layer {
        true => Term::Settled(step.apply(types, ty)),
        false => Term::Bottom,
    }
}

fn solve(
    members: &[ActivationKey],
    member_set: &HashSet<ActivationKey>,
    bindings: &Bindings,
    member_slots: &[(ActivationKey, usize)],
    types: &mut Types,
) -> Solved {
    let mut equations = Equations::new(member_set, bindings);
    let seeds: Vec<Unknown> = members
        .iter()
        .map(|member| Unknown::Return(member.clone()))
        .chain(
            member_slots
                .iter()
                .map(|(activation, slot)| Unknown::Slot(activation.clone(), *slot)),
        )
        .collect();
    equations.build(seeds, types);
    let escapes = equations.escapes();
    let pending = equations.pending();

    // Only escaping nodes get a body, so only they take a slot in the vector
    // handed to the interner; every other reference resolves to a concrete
    // type instead.
    let mut interned_index: Vec<Option<usize>> = vec![None; equations.nodes.len()];
    let mut interned_count = 0;
    for (node, escaping) in escapes.iter().enumerate() {
        if *escaping {
            interned_index[node] = Some(interned_count);
            interned_count += 1;
        }
    }

    let none_ty = types.none();
    let tys = match interned_count {
        0 => Vec::new(),
        _ => {
            let mut solver = Solver {
                equations: &equations,
                escapes: &escapes,
                interned_index: &interned_index,
                none_ty,
                types,
                bodies: vec![None; interned_count],
            };
            for (node, interned) in interned_index.iter().enumerate() {
                let Some(body_index) = *interned else {
                    continue;
                };
                let mut lowered: Option<DescrOf<ComponentRef>> = None;
                for branch in &equations.branches[node] {
                    let Some(branch_body) = solver.lower_branch(branch) else {
                        continue;
                    };
                    lowered = Some(match lowered {
                        Some(acc) => union_regular_bodies(&acc, &branch_body),
                        None => branch_body,
                    });
                }
                let body = lowered.unwrap_or_else(|| {
                    let unknown = &equations.nodes[node];
                    panic!("{unknown:?} was classified as escaping but every flattened branch failed to lower")
                });
                solver.bodies[body_index] = Some(body);
            }
            let Solver { bodies, types, .. } = solver;
            let bodies: Vec<DescrOf<ComponentRef>> = bodies
                .into_iter()
                .map(|body| body.expect("every escaping node's body is filled"))
                .collect();
            types.intern_regular_bodies(bodies)
        }
    };

    // Three answers, not two: a node still resting on something nothing has
    // observed has no answer to publish at all, which is not the same as a
    // node no value ever reaches (the empty type) or a node with no evidence
    // whatsoever.
    let answer = |node: usize| -> Option<Ty> {
        if pending[node] || equations.branches[node].is_empty() {
            return None;
        }
        match interned_index[node] {
            Some(body_index) => Some(tys[body_index]),
            None => Some(none_ty),
        }
    };

    // Auxiliary unknowns stand for interior positions and are never read
    // back: only whole activations have facts. Member returns become
    // `ReturnType`, member slots become that member's own input evidence.
    let mut result = Solved::default();
    for member in members {
        let node = equations.index[&Unknown::Return(member.clone())];
        if let Some(ty) = answer(node) {
            result.returns.insert(member.clone(), ty);
        }
    }
    for (node, unknown) in equations.nodes.iter().enumerate() {
        let Unknown::Slot(activation, slot) = unknown else {
            continue;
        };
        if let Some(ty) = answer(node) {
            let surfaces = slot_surfaces(&equations.branches[node], bindings);
            result
                .slots
                .insert((activation.clone(), *slot), ActivationInput::from_parts(ty, surfaces));
        }
    }
    result
}

/// What one component solve settles: every member's return, and every
/// member's parameter slots. Both come out of the one equation system and
/// the one `Types::intern_regular_bodies` call, so a member's accumulator
/// and the return that feeds it share a single recursive type.
#[derive(Debug, Default)]
struct Solved {
    returns: HashMap<ActivationKey, Ty>,
    slots: HashMap<(ActivationKey, usize), ActivationInput>,
}

/// Lowers already-flattened branches to `DescrOf<ComponentRef>`, one
/// equation node at a time. Every structural child is already a node of the
/// same system, so this walk mints nothing: it only resolves.
struct Solver<'a> {
    equations: &'a Equations<'a>,
    escapes: &'a [bool],
    interned_index: &'a [Option<usize>],
    none_ty: Ty,
    types: &'a mut Types,
    bodies: Vec<Option<DescrOf<ComponentRef>>>,
}

impl Solver<'_> {
    /// The reference a structural-child position lowers to. A node that
    /// escapes is a recursive edge; a node with branches that never escape
    /// is the empty type, computed; a node with no branches at all has no
    /// evidence, which drops the branch holding it.
    fn child_ref(&self, child: &Term) -> Option<ComponentRef> {
        match child {
            Term::Bottom | Term::Unobserved => None,
            Term::Settled(ty) => Some(ComponentRef::Published(*ty)),
            Term::Evidence(activation, slot) => self
                .equations
                .bindings
                .evidence
                .get(&(activation.clone(), *slot))
                .map(|input| ComponentRef::Published(input.ty())),
            other => {
                let unknown = self.equations.child_unknown(other)?;
                let node = *self.equations.index.get(&unknown)?;
                match self.interned_index[node] {
                    Some(body_index) => Some(ComponentRef::local(body_index)),
                    None if !self.equations.branches[node].is_empty() => {
                        debug_assert!(!self.escapes[node], "a node with a body would have been interned");
                        Some(ComponentRef::Published(self.none_ty))
                    }
                    None => None,
                }
            }
        }
    }

    fn lower_branch(&mut self, branch: &Term) -> Option<DescrOf<ComponentRef>> {
        match branch {
            Term::Bottom | Term::Unobserved => None,
            Term::Settled(ty) => Some(self.types.regular_published(*ty)),
            Term::Evidence(_, _) | Term::Return(_) | Term::Slot(_, _) => match self.child_ref(branch)? {
                ComponentRef::Published(ty) => Some(self.types.regular_published(ty)),
                // A bare reference to another node cannot become a whole
                // descriptor on its own -- `DescrOf` carries structure,
                // never a raw reference -- so this alternative contributes
                // nothing here; the node it names still reaches this one
                // normally wherever it sits as a real structural child.
                ComponentRef::Local(_) => None,
            },
            Term::Shape(_, shape) => {
                let children = self.equations.branch_children(branch);
                match shape {
                    Skeleton::Tuple(_) => {
                        let elements = children
                            .iter()
                            .map(|child| self.child_ref(child))
                            .collect::<Option<Vec<_>>>()?;
                        Some(DescrOf::tuple_of(elements))
                    }
                    Skeleton::List { non_empty, .. } => {
                        let element = self.child_ref(children.first()?)?;
                        Some(match non_empty {
                            true => DescrOf::non_empty_list_of(element),
                            false => DescrOf::list_of(element),
                        })
                    }
                    Skeleton::Map(fields) => {
                        let fields = fields
                            .iter()
                            .zip(children.iter())
                            .map(|((key, _), child)| Some((key.clone(), self.child_ref(child)?)))
                            .collect::<Option<BTreeMap<MapKey, ComponentRef>>>()?;
                        Some(DescrOf::map_of(fields))
                    }
                    Skeleton::Struct(module, fields) => {
                        let mut lowered = Vec::with_capacity(fields.len());
                        for ((key, _), child) in fields.iter().zip(children.iter()) {
                            let MapKey::Atom(field) = key else {
                                panic!("struct field key is not an atom: {key:?}");
                            };
                            lowered.push((field.clone(), self.child_ref(child)?));
                        }
                        let name = self
                            .equations
                            .bindings
                            .module_names
                            .get(module)
                            .expect("a struct brand names a module the world can name")
                            .clone();
                        Some(self.types.regular_struct_map(*module, name, lowered))
                    }
                    _ => None,
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "return_component_test.rs"]
mod return_component_test;
