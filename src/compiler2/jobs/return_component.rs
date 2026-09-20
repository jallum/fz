//! Solves every member's `ReturnType` for one recursive-return component at
//! once. `World::return_component` derives membership and the component's
//! canonical owner fresh from `ActivationAnalysis.callsites` and
//! `CallSiteTargets`; this job trusts a fresh recomputation of that same
//! query every time it runs, self-abdicating the moment it is no longer
//! that owner. Unlike `DeriveTypeDef`'s abdication (a `@type` equation's
//! component never reshapes once parsed, so it never needs to be woken
//! again), a return component's boundary genuinely moves as call targets
//! resolve, so abdication here still declares [`frontier_reads`]: the EDGE
//! facts (never a forward-cone node's whole `ActivationAnalyzed`) that
//! could redraw the boundary `World::return_flow_frontier` walked to find
//! it. That subscription is what attributes the abdication to a real cause
//! and lets this job be re-woken if ownership ever returns.
//!
//! # Guardedness
//!
//! A member's `ReturnExpression` may reference another member (or itself)
//! two ways: *guarded*, nested inside a real constructor (`Tuple`, `List`,
//! ...), or *unguarded*, as a bare `Local` alternative of a `Union` (or the
//! whole top-level expression). An unguarded reference carries no
//! information of its own — the least fixed point of `x = x | y` is just
//! `y` — so [`flatten`] inlines every member's own top-level unguarded
//! references away before anything is lowered. A guarded reference is left
//! alone: it already denotes the standard regular/equi-recursive type over
//! however many times its cycle actually unfolds, which `ComponentRef::Local`
//! represents directly.
//!
//! # Escaping
//!
//! A guarded branch can still be unresolvable if a nested reference names a
//! member with no evidence of its own — the branch depends on a value that
//! provably never exists. [`solve`] computes, for every member, whether it
//! *contributes* (has at least one flattened branch every nested reference
//! of which itself contributes or is external) as the least fixed point of
//! a monotone system over the finite member set. A member with flattened
//! branches but none that contribute is a productive cycle with no base
//! case: its least fixed point is the empty type, published as `none` — a
//! real, computed fact, never confused with the no-evidence case (no
//! flattened branches at all), which publishes nothing. A contributing
//! member's surviving branches lower to one `DescrOf<ComponentRef>` each,
//! folded by `union_regular_bodies`, and every contributing member's body
//! goes to `Types::intern_regular_bodies` in the same call: the interner's
//! own bisimulation partition refinement is what collapses two members
//! whose bodies turn out identical, so this job never needs a separate
//! closure-comparison step.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use super::super::drive::{Derivation, DerivationKey, FactKey, Job, JobEffects, current_uses};
use super::super::identity::{ActivationKey, ActivationSignature};
use super::super::scheduler::FatalError;
use super::super::semantic::{ActivationInput, ProjectStep, ReturnExpression, SemanticOrd as _};
use super::super::types::{ComponentRef, DescrOf, MapKey, Ty, Types, union_regular_bodies};
use super::super::world::World;

pub(super) fn solve_return_component(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    owner: &ActivationKey,
) -> Result<JobEffects, FatalError> {
    let Some(component) = world.return_component(owner) else {
        return Ok(JobEffects {
            reads: current_uses(frontier_reads(world, owner)),
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
            reads: current_uses(frontier_reads(world, owner)),
            ..JobEffects::default()
        });
    }
    let members = component.members;
    let member_set: HashSet<ActivationKey> = members.iter().cloned().collect();

    // `World::return_component`'s SCC walk can visit activations beyond
    // `members` on its way to (or past) `owner`'s component -- any of their
    // out-edges (`CallSiteTargets`, keyed off their function's STATIC
    // callsite set) moving can redraw the boundary the walk finds, so the
    // subscription has to cover the whole frontier, not just the settled
    // members. A member is different: its `ReturnExpression` is the
    // solver's actual input, so each member's own `ActivationAnalyzed` is
    // read explicitly below, alongside the frontier's edge facts.
    let mut reads: Vec<FactKey> = frontier_reads(world, owner);
    let mut waits = Vec::new();
    let mut expressions: HashMap<ActivationKey, ReturnExpression> = HashMap::new();
    for member in &members {
        reads.push(FactKey::ActivationAnalyzed(member.clone()));
        match world.activation_analysis(member) {
            Some(analysis) => {
                expressions.insert(member.clone(), analysis.expression.clone());
            }
            None => waits.push(FactKey::ActivationAnalyzed(member.clone())),
        }
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    // A member's `ReturnExpression` can name one of its own parameter slots
    // (`ReturnExpression::Input`) -- and so can another member's ARGUMENT
    // expression at a call site that targets it. Those input-side equations
    // live in `World::argument_flow`, one member's worth of per-slot
    // evidence at a time, and every slot of every member is an unknown of
    // this same system: a slot's evidence can name a further slot (its own
    // component's accumulator feeding a sibling's accumulator), and the
    // solved value of every slot is published back as the member's own
    // input evidence below, so none of them may be left out.
    let mut member_slots: Vec<(ActivationKey, usize)> = Vec::new();
    let mut slot_expressions: HashMap<(ActivationKey, usize), ReturnExpression> = HashMap::new();
    for member in &members {
        // A slot's evidence is contributed by this member's CALLERS, so it
        // is read, never waited on: an absent contribution is the ascent's
        // bottom so far, exactly as an absent external `ReturnType` is, and
        // the read alone re-wakes this solve when a caller's analysis raises
        // it. Waiting would deadlock the moment a caller sat inside the
        // component it feeds.
        reads.push(FactKey::ArgumentFlow(member.clone()));
        let flow = world.argument_flow(member).cloned();
        for slot in 0..member.input_len() {
            let Some(expression) = flow.as_ref().and_then(|flow| flow.slot(slot)) else {
                continue;
            };
            // Every slot's evidence is available to the system: a member's
            // return may name any of them, and the solver resolves such a
            // reference through this map. Only a slot fed from INSIDE the
            // component is seeded as an unknown in its own right, though. A
            // slot no member names and whose own evidence names no member is
            // already settled by its callers' contributions -- seeding it
            // would restate them and pull their whole (arbitrarily wide)
            // evidence into the system for nothing.
            if names_member(expression, &member_set) {
                member_slots.push((member.clone(), slot));
            }
            slot_expressions.insert((member.clone(), slot), expression.clone());
        }
    }

    // Every `Local` the members' returns OR their slots' evidence names
    // outside the component is a real data dependency, but never a wait:
    // exactly like ordinary function calls (`prepare_function_call`), a
    // still-absent external return is the ascent's bottom so far, not a
    // block, and the read alone is the subscription that re-wakes this
    // solve when the external's evidence rises. Waiting here would
    // deadlock the moment two components' owners depended on each other's
    // members.
    let mut external_keys = Vec::new();
    for expression in expressions.values() {
        expression.locals(&mut external_keys);
    }
    for expression in slot_expressions.values() {
        expression.locals(&mut external_keys);
    }
    external_keys.retain(|key| !member_set.contains(key));
    external_keys.sort_by(|a, b| a.semantic_cmp(b, world.types()));
    let mut externals: HashMap<ActivationKey, Ty> = HashMap::new();
    for external in &external_keys {
        reads.push(FactKey::ReturnType(external.clone()));
        if let Some(ty) = world.activation_return(external) {
            externals.insert(external.clone(), ty);
        }
    }

    // A slot equation reaches OUT of the component whenever a non-member
    // calls a member: the caller's own parameter is the value that arrives.
    // What that parameter holds is the evidence the caller's walk
    // contributed -- its type together with the callable surfaces observed at
    // it -- and never the caller's key coordinate. A key coordinate names a
    // position: `fun` stands there for "some callable", so a solve reading it
    // would answer with a value no walk ever saw, the closure behind it would
    // lose its clauses, and the call through it would widen to `any`. The
    // evidence is a read, and an evidence-less caller is waited for rather
    // than substituted for.
    let mut external_slot_keys = Vec::new();
    for expression in expressions.values().chain(slot_expressions.values()) {
        expression.input_slots(&mut external_slot_keys);
    }
    external_slot_keys.retain(|(activation, _)| !member_set.contains(activation));
    external_slot_keys.sort_by(|left, right| left.0.semantic_cmp(&right.0, world.types()).then(left.1.cmp(&right.1)));
    let mut external_slots: HashMap<(ActivationKey, usize), ActivationInput> = HashMap::new();
    let mut evidence_waits = Vec::new();
    for (activation, slot) in external_slot_keys {
        reads.push(FactKey::ActivationInputs(activation.clone()));
        match world
            .activation_input_alternatives(&activation)
            .and_then(|alternatives| alternatives.joined().get(slot).cloned())
        {
            Some(input) => {
                external_slots.insert((activation, slot), input);
            }
            None => evidence_waits.push(FactKey::ActivationInputs(activation)),
        }
    }
    if !evidence_waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(evidence_waits),
            ..JobEffects::default()
        });
    }

    let types = world.types_mut();
    let solved = solve(
        &members,
        &member_set,
        &expressions,
        &member_slots,
        &slot_expressions,
        &externals,
        &external_slots,
        types,
    );

    let mut outputs = Vec::new();
    let mut changed = Vec::new();
    for member in &members {
        let fact = FactKey::ReturnType(member.clone());
        outputs.push(fact.clone());
        // Bottom rule: a member with no flattened branch anywhere in the
        // component publishes no VALUE, only settling its claim at empty
        // content -- exactly `AnalyzeActivation`'s own established bottom
        // representation for a non-member activation with no evidence yet
        // (`define_return`'s `None`-evidence arm is a genuine no-op against
        // an empty store). Leaving the fact undeclared here instead would
        // starve any waiter forever: nothing else can ever settle it.
        let evidence = solved.returns.get(member).copied();
        let derivation = Derivation::of(
            Job::SolveReturnComponent(owner.clone()),
            DerivationKey::Activation(member.clone()),
        );
        if super::super::drive::ExecutionContext::new(world, tel).define_activation_return(&derivation, evidence) {
            changed.push(fact);
        }
    }

    // The same solve settles each member's own INPUT evidence. A member's
    // slot equation is the join of every call site's argument expression, so
    // its solution is the closed form of an accumulator that would otherwise
    // be discovered one nesting at a time -- one rung per re-analysis, each
    // rung a fresh activation key. Contributing it back through the ordinary
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
        reads: current_uses(reads),
        outputs,
        changed,
        activation_input_contributions,
        ..JobEffects::default()
    })
}

/// The read set that explains why `world.return_component(owner)` currently
/// draws the boundary it does: `FactKey::CallSiteTargets` for every callsite
/// of every activation `World::return_flow_frontier` visited while
/// establishing it, member or not. A change to any of these edge facts is
/// what could redraw the boundary (grow it, shrink it, hand ownership to a
/// different member), so it is a real, attributable cause instead of an
/// empty read set masquerading as one. A cone node's own
/// `ActivationAnalyzed` is deliberately NOT read here — its analysis moving
/// for reasons that leave its callsite targets untouched has no bearing on
/// this boundary, and reading it anyway is exactly the excess-churn source
/// this function replaces (see [`static_callsite_reads`]).
fn frontier_reads(world: &World, owner: &ActivationKey) -> Vec<FactKey> {
    world
        .return_flow_frontier(owner)
        .into_iter()
        .flat_map(|key| static_callsite_reads(world, &key))
        .collect()
}

/// `FactKey::CallSiteTargets` for every callsite named by the STATIC lowered
/// body of `activation`'s function (`body::callsite_input_modes`, a pure
/// scan over the function's `LoweredBody` entries) — the edge facts whose
/// movement could actually grow, shrink, or retarget the SCC walk through
/// this node. This is deliberately the function's whole structural callsite
/// set, not `activation`'s own dynamic `ActivationAnalysis.callsites` (which
/// is filtered down to whatever that one activation's analysis happened to
/// resolve): the static set is activation-independent, so it never needs
/// `activation`'s `ActivationAnalyzed` fact to enumerate, which is the whole
/// point — a non-member cone node's analysis moving is not itself a cause
/// this job needs to track. Falls back to a `FactKey::LoweredBody` read when
/// the function has not been lowered yet: the callsite set is undefined
/// until then, and that absence is itself an ordinary read of an absent
/// fact, waking this job once lowering completes.
fn static_callsite_reads(world: &World, activation: &ActivationKey) -> Vec<FactKey> {
    let lowered_fact = FactKey::LoweredBody(activation.function);
    if !world.has_fact(&lowered_fact) {
        return vec![lowered_fact];
    }
    let body = world.lowered_body(activation.function);
    super::super::body::callsite_input_modes(&body)
        .into_keys()
        .map(|callsite| {
            FactKey::CallSiteTargets(super::super::semantic::CallSiteKey {
                activation: activation.clone(),
                callsite,
            })
        })
        .collect()
}

/// Whether an expression names any activation in `members`, as a whole
/// return (`Local`) or as one of their parameter slots (`Input`). This is
/// what makes a slot an unknown of the component's system rather than a
/// value its callers have already settled.
fn names_member(expression: &ReturnExpression, members: &HashSet<ActivationKey>) -> bool {
    match expression {
        ReturnExpression::Bottom | ReturnExpression::Published(_) => false,
        ReturnExpression::Local(key) => members.contains(key),
        ReturnExpression::Input { activation, .. } => members.contains(activation),
        ReturnExpression::Union(branches) => branches.iter().any(|b| names_member(b, members)),
        ReturnExpression::Tuple(elems) => elems.iter().any(|e| names_member(e, members)),
        ReturnExpression::List(elem) | ReturnExpression::NonEmptyList(elem) => names_member(elem, members),
        ReturnExpression::Map(fields) => fields.iter().any(|(_, v)| names_member(v, members)),
        ReturnExpression::Struct(_, _, fields) => fields.iter().any(|(_, v)| names_member(v, members)),
        ReturnExpression::Project { of, .. } => names_member(of, members),
    }
}

/// One unknown of the component's equation system. A member's whole return
/// and a member's parameter slot are the unknowns the component is named
/// for. An auxiliary unknown stands for every other position that needs a
/// node of its own: a constructor's child, and a projection read back out of
/// a value whose own shape is still symbolic. Auxiliary unknowns are keyed
/// by the expression itself, so the same position met twice along two paths
/// is one node — which is what makes unfolding a projection around a cycle
/// terminate at the cycle instead of climbing it one rung at a time.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Unknown {
    Return(ActivationKey),
    Slot(ActivationKey, usize),
    Aux(ReturnExpression),
}

/// The equation system: one node per [`Unknown`], each carrying the
/// flattened branches its own value is the union of. Every reference a
/// branch makes at a structural-child position is itself a node here, so the
/// whole system is a finite graph over subterms of the members' analyses,
/// ready to hand to `Types::intern_regular_bodies` in one call.
struct Equations<'a> {
    members: &'a HashSet<ActivationKey>,
    expressions: &'a HashMap<ActivationKey, ReturnExpression>,
    slot_expressions: &'a HashMap<(ActivationKey, usize), ReturnExpression>,
    externals: &'a HashMap<ActivationKey, Ty>,
    external_slots: &'a HashMap<(ActivationKey, usize), ActivationInput>,
    index: HashMap<Unknown, usize>,
    nodes: Vec<Unknown>,
    branches: Vec<Vec<ReturnExpression>>,
}

impl<'a> Equations<'a> {
    fn new(
        members: &'a HashSet<ActivationKey>,
        expressions: &'a HashMap<ActivationKey, ReturnExpression>,
        slot_expressions: &'a HashMap<(ActivationKey, usize), ReturnExpression>,
        externals: &'a HashMap<ActivationKey, Ty>,
        external_slots: &'a HashMap<(ActivationKey, usize), ActivationInput>,
    ) -> Self {
        Self {
            members,
            expressions,
            slot_expressions,
            externals,
            external_slots,
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

    /// The equation a node's value is defined by: a member's own analysed
    /// return, a slot's joined argument evidence, or the auxiliary
    /// expression the node stands for.
    fn equation(&self, unknown: &Unknown) -> ReturnExpression {
        match unknown {
            Unknown::Return(key) => self.expressions.get(key).cloned().unwrap_or(ReturnExpression::Bottom),
            Unknown::Slot(key, slot) => self
                .slot_expressions
                .get(&(key.clone(), *slot))
                .cloned()
                .unwrap_or(ReturnExpression::Bottom),
            Unknown::Aux(expression) => expression.clone(),
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
                // a function of the members' analyses rather than of the round
                // a branch happened to arrive in.
                let standing: HashSet<&ReturnExpression> = self.branches[next].iter().collect();
                let arrived: Vec<ReturnExpression> = computed
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
                    .iter()
                    .flat_map(branch_children)
                    .filter_map(|child| child_unknown(child, self.members))
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
    fn expand_node(&mut self, unknown: &Unknown, types: &mut Types) -> Vec<ReturnExpression> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        if let Unknown::Aux(ReturnExpression::Project { of, step }) = unknown {
            // A projection reads one layer out of whatever its subject
            // denotes. Its subject's branches are already constructors or
            // leaves, so reading through them is a step DOWN into subterms,
            // never a further unfolding of the cycle the subject sits on.
            let mut inner = Vec::new();
            let mut inner_seen = HashSet::new();
            self.expand_into(of, &mut inner, &mut inner_seen);
            for branch in inner {
                let projected = project_branch(&branch, step, self.externals, self.external_slots, types);
                self.expand_into(&projected, &mut out, &mut seen);
            }
            return out;
        }
        let equation = self.equation(unknown);
        self.expand_into(&equation, &mut out, &mut seen);
        out
    }

    /// Adds what `expr` denotes to `out`: a constructor or leaf is itself a
    /// branch, a union contributes each alternative, and an unguarded
    /// reference contributes its referent node's current branches.
    fn expand_into(
        &mut self,
        expr: &ReturnExpression,
        out: &mut Vec<ReturnExpression>,
        seen: &mut HashSet<ReturnExpression>,
    ) {
        match expr {
            ReturnExpression::Bottom => {}
            ReturnExpression::Union(branches) => {
                for branch in branches {
                    self.expand_into(branch, out, seen);
                }
            }
            ReturnExpression::Local(key) if self.members.contains(key) => {
                let node = self.node(Unknown::Return(key.clone()));
                self.absorb(node, out, seen);
            }
            ReturnExpression::Input { activation, slot, .. } if self.members.contains(activation) => {
                let node = self.node(Unknown::Slot(activation.clone(), *slot));
                self.absorb(node, out, seen);
            }
            ReturnExpression::Project { .. } => {
                let node = self.node(Unknown::Aux(expr.clone()));
                self.absorb(node, out, seen);
            }
            other => {
                if seen.insert(other.clone()) {
                    out.push(other.clone());
                }
            }
        }
    }

    fn absorb(&self, node: usize, out: &mut Vec<ReturnExpression>, seen: &mut HashSet<ReturnExpression>) {
        for branch in &self.branches[node] {
            if seen.insert(branch.clone()) {
                out.push(branch.clone());
            }
        }
    }

    /// The least fixed point of "this node reaches a value": a node escapes
    /// once one of its branches does, and a branch escapes once every
    /// structural child position it fills escapes. A node with branches that
    /// never escapes is a productive cycle with no base case -- its value is
    /// the empty type. A node with no branches at all has no evidence yet,
    /// which is a different state entirely.
    fn escapes(&self) -> Vec<bool> {
        let mut escapes = vec![false; self.nodes.len()];
        loop {
            let mut advanced = false;
            for node in 0..self.nodes.len() {
                if escapes[node] {
                    continue;
                }
                if self.branches[node]
                    .iter()
                    .any(|branch| self.branch_escapes(branch, &escapes))
                {
                    escapes[node] = true;
                    advanced = true;
                }
            }
            if !advanced {
                break;
            }
        }
        escapes
    }

    /// Whether a flattened branch -- a whole body in its own right -- reaches
    /// a value. Mirrors [`Solver::lower_branch`] arm for arm: a bare
    /// reference cannot become a whole descriptor (a `DescrOf` carries
    /// structure, never a raw reference), so only a reference resolving to a
    /// concrete external type escapes here.
    fn branch_escapes(&self, branch: &ReturnExpression, escapes: &[bool]) -> bool {
        match branch {
            ReturnExpression::Bottom => false,
            ReturnExpression::Published(_) => true,
            ReturnExpression::Local(key) => self.externals.contains_key(key),
            ReturnExpression::Input { activation, slot } => {
                self.external_slots.contains_key(&(activation.clone(), *slot))
            }
            ReturnExpression::Project { .. } => false,
            ReturnExpression::Union(branches) => branches.iter().any(|b| self.branch_escapes(b, escapes)),
            ReturnExpression::Tuple(elems) => elems.iter().all(|e| self.child_escapes(e, escapes)),
            ReturnExpression::List(elem) | ReturnExpression::NonEmptyList(elem) => self.child_escapes(elem, escapes),
            ReturnExpression::Map(fields) | ReturnExpression::Struct(_, _, fields) => {
                fields.iter().all(|(_, value)| self.child_escapes(value, escapes))
            }
        }
    }

    /// Whether a structural-child position escapes. Unlike a whole-body
    /// position, a reference here is a normal recursive edge (it lowers to a
    /// `ComponentRef`, not a `DescrOf`), so it escapes exactly when the node
    /// it names does. Mirrors [`Solver::child_ref`].
    fn child_escapes(&self, child: &ReturnExpression, escapes: &[bool]) -> bool {
        match child {
            ReturnExpression::Bottom => false,
            ReturnExpression::Published(_) => true,
            ReturnExpression::Local(key) if !self.members.contains(key) => self.externals.contains_key(key),
            ReturnExpression::Input { activation, slot } if !self.members.contains(activation) => {
                self.external_slots.contains_key(&(activation.clone(), *slot))
            }
            other => match child_unknown(other, self.members).and_then(|unknown| self.index.get(&unknown)) {
                Some(&node) => escapes[node],
                None => false,
            },
        }
    }
}

/// The structural-child positions of one flattened branch: the positions
/// that lower to a `ComponentRef` rather than to a descriptor of their own.
fn branch_children(branch: &ReturnExpression) -> Vec<&ReturnExpression> {
    match branch {
        ReturnExpression::Tuple(elems) => elems.iter().collect(),
        ReturnExpression::List(elem) | ReturnExpression::NonEmptyList(elem) => vec![elem],
        ReturnExpression::Map(fields) | ReturnExpression::Struct(_, _, fields) => {
            fields.iter().map(|(_, value)| value).collect()
        }
        _ => Vec::new(),
    }
}

/// The node a structural child needs, if any. A concrete type and a
/// reference to something outside the component both carry their own value
/// already; everything else -- an in-component reference, a nested union, a
/// nested constructor, a surviving projection -- is an equation node.
fn child_unknown(child: &ReturnExpression, members: &HashSet<ActivationKey>) -> Option<Unknown> {
    match child {
        ReturnExpression::Bottom | ReturnExpression::Published(_) => None,
        ReturnExpression::Local(key) => members.contains(key).then(|| Unknown::Return(key.clone())),
        ReturnExpression::Input { activation, slot, .. } => members
            .contains(activation)
            .then(|| Unknown::Slot(activation.clone(), *slot)),
        other => Some(Unknown::Aux(other.clone())),
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
fn slot_surfaces(
    branches: &[ReturnExpression],
    external_slots: &HashMap<(ActivationKey, usize), ActivationInput>,
) -> BTreeSet<ActivationSignature> {
    branches
        .iter()
        .filter_map(|branch| match branch {
            ReturnExpression::Input { activation, slot } => external_slots.get(&(activation.clone(), *slot)),
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
fn project_concrete(ty: Ty, step: &ProjectStep, types: &mut Types) -> ReturnExpression {
    let carries_the_layer = match step {
        ProjectStep::ListElement | ProjectStep::ListTail => types.has_list_shape(&ty),
        ProjectStep::TupleField(index) => types.max_tuple_arity(&ty) > *index,
        // A key the type does not promise is exactly the case the ordinary
        // walk answers `any` for, and the two views have to agree.
        ProjectStep::MapField(_) => true,
    };
    match carries_the_layer {
        true => ReturnExpression::Published(step.apply(types, ty)),
        false => ReturnExpression::Bottom,
    }
}

/// Reads one layer out of a single already-flattened branch. Every
/// in-component reference has been inlined by the time a branch reaches
/// here, so a surviving reference names something outside the component and
/// carries its own concrete type; a constructor hands back the companion it
/// already holds at that position; a branch built from a different
/// constructor promises no such layer at all, which is the empty type.
fn project_branch(
    branch: &ReturnExpression,
    step: &ProjectStep,
    externals: &HashMap<ActivationKey, Ty>,
    external_slots: &HashMap<(ActivationKey, usize), ActivationInput>,
    types: &mut Types,
) -> ReturnExpression {
    match branch {
        ReturnExpression::Bottom => ReturnExpression::Bottom,
        ReturnExpression::Published(ty) => project_concrete(*ty, step, types),
        ReturnExpression::Local(key) => match externals.get(key) {
            Some(&ty) => project_concrete(ty, step, types),
            None => ReturnExpression::Bottom,
        },
        ReturnExpression::Input { activation, slot } => match external_slots.get(&(activation.clone(), *slot)) {
            Some(input) => project_concrete(input.ty(), step, types),
            None => ReturnExpression::Bottom,
        },
        ReturnExpression::Union(branches) => branches
            .iter()
            .map(|branch| project_branch(branch, step, externals, external_slots, types))
            .fold(ReturnExpression::Bottom, ReturnExpression::union),
        ReturnExpression::Tuple(elems) => match step {
            ProjectStep::TupleField(index) => elems.get(*index).cloned().unwrap_or(ReturnExpression::Bottom),
            _ => ReturnExpression::Bottom,
        },
        ReturnExpression::List(elem) | ReturnExpression::NonEmptyList(elem) => match step {
            ProjectStep::ListElement => (**elem).clone(),
            ProjectStep::ListTail => ReturnExpression::List(elem.clone()),
            _ => ReturnExpression::Bottom,
        },
        ReturnExpression::Map(fields) | ReturnExpression::Struct(_, _, fields) => match step {
            // A key the companion does not carry is exactly the case the
            // observed type answers `any` for, and the two views have to
            // agree.
            ProjectStep::MapField(wanted) => fields
                .iter()
                .find(|(key, _)| key == wanted)
                .map(|(_, value)| value.clone())
                .unwrap_or_else(|| ReturnExpression::Published(types.any())),
            _ => ReturnExpression::Bottom,
        },
        ReturnExpression::Project { .. } => ReturnExpression::Bottom,
    }
}

fn solve(
    members: &[ActivationKey],
    member_set: &HashSet<ActivationKey>,
    expressions: &HashMap<ActivationKey, ReturnExpression>,
    member_slots: &[(ActivationKey, usize)],
    slot_expressions: &HashMap<(ActivationKey, usize), ReturnExpression>,
    externals: &HashMap<ActivationKey, Ty>,
    external_slots: &HashMap<(ActivationKey, usize), ActivationInput>,
    types: &mut Types,
) -> Solved {
    let mut equations = Equations::new(member_set, expressions, slot_expressions, externals, external_slots);
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
    let mut result = Solved::default();
    if interned_count == 0 {
        for member in members {
            let node = equations.index[&Unknown::Return(member.clone())];
            if !equations.branches[node].is_empty() {
                result.returns.insert(member.clone(), none_ty);
            }
        }
        for (node, unknown) in equations.nodes.iter().enumerate() {
            let Unknown::Slot(activation, slot) = unknown else {
                continue;
            };
            if !equations.branches[node].is_empty() {
                let surfaces = slot_surfaces(&equations.branches[node], external_slots);
                result.slots.insert(
                    (activation.clone(), *slot),
                    ActivationInput::from_parts(none_ty, surfaces),
                );
            }
        }
        return result;
    }

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
    let tys = types.intern_regular_bodies(bodies);

    // Auxiliary unknowns stand for interior positions and are never read
    // back: only whole activations have facts. Member returns become
    // `ReturnType`, member slots become that member's own input evidence.
    for member in members {
        let node = equations.index[&Unknown::Return(member.clone())];
        match interned_index[node] {
            Some(body_index) => {
                result.returns.insert(member.clone(), tys[body_index]);
            }
            None if !equations.branches[node].is_empty() => {
                result.returns.insert(member.clone(), none_ty);
            }
            None => {}
        }
    }
    for (node, unknown) in equations.nodes.iter().enumerate() {
        let Unknown::Slot(activation, slot) = unknown else {
            continue;
        };
        let solved_ty = match interned_index[node] {
            Some(body_index) => Some(tys[body_index]),
            None if !equations.branches[node].is_empty() => Some(none_ty),
            None => None,
        };
        if let Some(ty) = solved_ty {
            let surfaces = slot_surfaces(&equations.branches[node], external_slots);
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
    fn child_ref(&self, child: &ReturnExpression) -> Option<ComponentRef> {
        match child {
            ReturnExpression::Bottom => None,
            ReturnExpression::Published(ty) => Some(ComponentRef::Published(*ty)),
            ReturnExpression::Local(key) if !self.equations.members.contains(key) => {
                self.equations.externals.get(key).map(|&ty| ComponentRef::Published(ty))
            }
            ReturnExpression::Input { activation, slot } if !self.equations.members.contains(activation) => self
                .equations
                .external_slots
                .get(&(activation.clone(), *slot))
                .map(|input| ComponentRef::Published(input.ty())),
            other => {
                let unknown = child_unknown(other, self.equations.members)?;
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

    fn lower_branch(&mut self, branch: &ReturnExpression) -> Option<DescrOf<ComponentRef>> {
        match branch {
            ReturnExpression::Bottom => None,
            ReturnExpression::Published(ty) => Some(self.types.regular_published(*ty)),
            ReturnExpression::Local(_) | ReturnExpression::Input { .. } | ReturnExpression::Project { .. } => {
                match self.child_ref(branch)? {
                    ComponentRef::Published(ty) => Some(self.types.regular_published(ty)),
                    // A bare reference to another node cannot become a whole
                    // descriptor on its own -- `DescrOf` carries structure,
                    // never a raw reference -- so this alternative contributes
                    // nothing here; the node it names still reaches this one
                    // normally wherever it sits as a real structural child.
                    ComponentRef::Local(_) => None,
                }
            }
            ReturnExpression::Union(branches) => {
                let mut result: Option<DescrOf<ComponentRef>> = None;
                for branch in branches {
                    let Some(lowered) = self.lower_branch(branch) else {
                        continue;
                    };
                    result = Some(match result {
                        Some(acc) => union_regular_bodies(&acc, &lowered),
                        None => lowered,
                    });
                }
                result
            }
            ReturnExpression::Tuple(elems) => {
                let elems = elems.iter().map(|e| self.child_ref(e)).collect::<Option<Vec<_>>>()?;
                Some(DescrOf::tuple_of(elems))
            }
            ReturnExpression::List(elem) => Some(DescrOf::list_of(self.child_ref(elem)?)),
            ReturnExpression::NonEmptyList(elem) => Some(DescrOf::non_empty_list_of(self.child_ref(elem)?)),
            ReturnExpression::Map(fields) => {
                let fields = fields
                    .iter()
                    .map(|(key, value)| Some((key.clone(), self.child_ref(value)?)))
                    .collect::<Option<BTreeMap<MapKey, ComponentRef>>>()?;
                Some(DescrOf::map_of(fields))
            }
            ReturnExpression::Struct(module, name, fields) => {
                let mut lowered = Vec::with_capacity(fields.len());
                for (key, value) in fields {
                    let MapKey::Atom(field) = key else {
                        panic!("struct field key is not an atom: {key:?}");
                    };
                    lowered.push((field.clone(), self.child_ref(value)?));
                }
                Some(self.types.regular_struct_map(*module, name.clone(), lowered))
            }
        }
    }
}

#[cfg(test)]
#[path = "return_component_test.rs"]
mod return_component_test;
