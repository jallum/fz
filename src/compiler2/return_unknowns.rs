//! Which positions of a return system are still being solved, decided from
//! the static skeletons alone.
//!
//! A call's key coordinate for one argument is decided by one question: is
//! the value that arrives there something the fixpoint has already settled,
//! or is it a position the fixpoint is still solving? Keying on the second
//! kind mints one activation per round of the ascent, because what the walk
//! observed there is how far the climb has got rather than what the program
//! denotes. Keying on the first kind is ordinary specialization and must be
//! kept: a token list that never moves is exactly what dispatch needs.
//!
//! The question is asked of [`return_skeleton`], never of an activation. An
//! answer read off an activation's own companions would be read from
//! evidence the answer then destroys: the moment a caller learns its callee
//! is a member it re-keys that callee on an address variable, the old
//! activation stops being named, the companion that proved membership
//! disappears, and membership goes away again. Statically there is nothing
//! to destroy -- the skeletons are fixed once the bodies are lowered, so the
//! same call is keyed the same way in its first round and in its last.
//!
//! A *position* is a function's whole return, one of its parameter slots,
//! one of its own call sites' results, or an interior place inside a
//! skeleton -- a layer read back out of a value whose own shape is still
//! symbolic. Two kinds of edge connect them, and the difference between them
//! is the whole discrimination:
//!
//! * a *bare* edge is an alias or a projection -- `x = y`, `x = field 2 of
//!   y`. A cycle of bare edges alone denotes a value entirely determined by
//!   what enters the cycle from outside it: the least solution of
//!   `rest = tail(rest) | [int]` is `[int]`, reached in one step and never
//!   moving again.
//! * a *guarded* edge crosses a constructor -- `x = [y]`, `x = {:ok, y, z}`.
//!   A cycle through one of those is productive: each turn wraps another
//!   layer, so the solution is a recursive type and the position genuinely
//!   is being solved.
//!
//! So an UNKNOWN is a position on a cycle that crosses at least one
//! constructor. That is how a helper joins a cycle it is not itself part of
//! -- `wrap(nest(rest))` puts `wrap`'s parameter slot on `nest`'s cycle --
//! and how an accumulator's consumer joins through the slot it is handed.
//!
//! Projections are reduced against the constructors they read, exactly as
//! `jobs::return_component`'s solver reduces them, so a constructor
//! immediately undone by a projection contributes no guard. That is what
//! keeps `rest`, field 2 of a parser's `{:ok, value, rest}`, a settled token
//! list rather than an unknown, while `value`, field 1 of the same tuple,
//! is an unknown.
//!
//! The walk that answers for one function follows that function's own
//! callees, transitively, and everything it publishes is a fact about what
//! THIS body does: whether its own return is being solved, which of its
//! slots that return is built from, and what each of its own call sites
//! hands on and takes back. A cycle those positions sit on runs through
//! calls this body makes and through the arguments it hands them, so it lies
//! inside that reach.
//!
//! What ARRIVES at a slot is deliberately not among them. A slot is written
//! by CALLERS, and a caller need not lie inside the callee's reach at all:
//! `wrap(v)` reaches nothing, yet the only value it is ever handed is a
//! recursive result still climbing. So "is this argument still climbing?" is
//! answered where the argument is written, by the caller whose own reach
//! does contain the cycle, and it is published per call site.
//!
//! One slot still gets one coordinate rule, so what a call site publishes
//! is not the shape of the single value it writes but the shape of its
//! DESTINATION SLOT, folded over every call site this walk can see feeding
//! it: a seed call handing `[]` and an ascent call handing `[x | acc]` land
//! in one position and must name it the same way, or the seed keys apart
//! from every round after it. It is the same fold either side would compute;
//! only the caller has the reach to compute it, because its reach contains
//! the callee's and, on top of that, the argument it writes itself.
//!
//! A call made THROUGH a value names no callee in any body, so this walk
//! cannot see past it: its arguments are recorded, and what it yields
//! reaches nothing. Everything this answer asks of a body is therefore
//! decided before any activation exists, which is the whole point -- an
//! answer derived from an activation's own companions would be derived from
//! evidence the answer then destroys.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use super::body::{CallInputMode, CallSiteId};
use super::identity::FunctionId;
use super::return_skeleton::{FunctionSkeleton, Returns, Skeleton};
use super::semantic::ProjectStep;
use super::types::{AddrStep, MapKey, Ty, Types};

/// One position of the static system.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Position {
    /// A function's whole return.
    Return(FunctionId),
    /// One of a function's parameter slots.
    Slot(FunctionId, usize),
    /// What one of a function's own call sites yields.
    Result(FunctionId, CallSiteId),
    /// An interior place, named by the skeleton standing at it in the
    /// vocabulary of the function that wrote it.
    Interior(FunctionId, Skeleton),
}

/// The position a skeleton stands at, when it is not itself a value that
/// carries its own answer. A constructor and a settled value answer for
/// themselves and need no node.
fn position_of(function: FunctionId, skeleton: &Skeleton) -> Option<Position> {
    match skeleton {
        Skeleton::Input(slot) => Some(Position::Slot(function, *slot)),
        Skeleton::Result { callsite, .. } => Some(Position::Result(function, *callsite)),
        Skeleton::Project { .. } => Some(Position::Interior(function, skeleton.clone())),
        // A ground value, a constructor and a union carry their own answer
        // rather than pointing at another position, so there is no node to
        // name. What a constructor GUARDS is found by descending into it
        // (`guarded_positions`), never by asking it for a position.
        Skeleton::Bottom
        | Skeleton::Ground(_)
        | Skeleton::Union(_)
        | Skeleton::Tuple(_)
        | Skeleton::List { .. }
        | Skeleton::Map(_)
        | Skeleton::Struct(_, _) => None,
    }
}

/// Every position one flattened branch guards: the references its
/// constructors hold, wherever they sit inside them.
///
/// Crossing ONE constructor is what makes an edge guarded, so a reference
/// held two constructors deep -- `{:ok, [rest]}` -- is guarded exactly as a
/// reference held one deep is, and reaching it means descending through the
/// inner constructor rather than stopping at it. A union inside a
/// constructor is not a constructor at all: it is a choice between what its
/// alternatives denote, so every alternative is held at the same place and
/// each one is guarded.
fn guarded_positions(function: FunctionId, branch: &Skeleton) -> Vec<Position> {
    let mut out = Vec::new();
    collect_guarded(function, branch, &mut out);
    out
}

fn collect_guarded(function: FunctionId, skeleton: &Skeleton, out: &mut Vec<Position>) {
    match skeleton {
        Skeleton::Tuple(elems) => {
            for elem in elems {
                collect_held(function, elem, out);
            }
        }
        Skeleton::List { element, .. } => collect_held(function, element, out),
        Skeleton::Map(fields) | Skeleton::Struct(_, fields) => {
            for (_, value) in fields {
                collect_held(function, value, out);
            }
        }
        _ => {}
    }
}

/// One place a constructor holds, resolved to the positions standing there.
fn collect_held(function: FunctionId, skeleton: &Skeleton, out: &mut Vec<Position>) {
    match skeleton {
        Skeleton::Union(alternatives) => {
            for alternative in alternatives {
                collect_held(function, alternative, out);
            }
        }
        Skeleton::Tuple(_) | Skeleton::List { .. } | Skeleton::Map(_) | Skeleton::Struct(_, _) => {
            collect_guarded(function, skeleton, out)
        }
        _ => out.extend(position_of(function, skeleton)),
    }
}

/// Whether `branch`, standing at `position`, holds `child` only by reading it
/// straight back out of `position`. `walk({:go, acc}, n)` calling
/// `walk({:go, acc}, n - 1)` puts `{:go, field 1 of slot 0}` at slot 0: each
/// turn takes the tuple apart and puts the same layer back, so the cycle it
/// closes grows nothing and its constructor guards nothing. It is the mirror
/// of the reduction `expand_node` already does for a projection that reads a
/// constructor -- there the projection undoes the constructor, here the
/// constructor undoes the projection.
///
/// The test is the reduction itself: project the branch at the step the child
/// reads, and the answer is the child exactly when the constructor put back
/// what the projection took. One more layer -- `{:go, [field 1 of slot 0]}` --
/// reduces to a LIST of the child and is productive, as it should be.
fn reconstructs(position: &Position, function: FunctionId, branch: &Skeleton, child: &Position) -> bool {
    let Position::Interior(child_function, projection @ Skeleton::Project { of, step }) = child else {
        return false;
    };
    *child_function == function
        && position_of(function, of).as_ref() == Some(position)
        && Skeleton::project(branch.clone(), step.clone()) == *projection
}

/// What one function's keying needs to know, and nothing else: whether its
/// own return is being solved, and what each of its call sites hands on and
/// yields.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct FunctionUnknowns {
    /// This function's return sits on a productive cycle, so an activation
    /// of it owes its return to a component solve rather than to its own
    /// walk.
    pub(crate) returns: bool,
    /// One entry per semantic input: whether this function's published
    /// return IS, CONTAINS, or is a PROJECTION OF the value that arrives
    /// there. The answer is reachability from `Return(f)` in the position
    /// graph, so it composes across call sites on its own -- a function that
    /// returns `g(x)` inherits whatever `g` does with its parameter.
    pub(crate) returned_inputs: Box<[bool]>,
    /// One entry per call site, by WHERE the call sits in this body.
    ///
    /// A `CallSiteId` also carries the span it was lowered from, and a span
    /// names the version of the source it came from, so re-submitting the
    /// same text mints ids that are unequal to the ones this answer was
    /// derived with. The body is what says which call is which, and this
    /// answer is already about one body, so the position alone identifies
    /// the site and the answer survives a re-submission that changed
    /// nothing.
    pub(crate) callsites: BTreeMap<u32, CallSiteUnknowns>,
}

impl FunctionUnknowns {
    pub(crate) fn callsite(&self, callsite: CallSiteId) -> Option<&CallSiteUnknowns> {
        self.callsites.get(&callsite.as_u32())
    }

    /// Whether a value arriving at `slot` can be read back out of what this
    /// function returns.
    pub(crate) fn returns_input(&self, slot: usize) -> bool {
        self.returned_inputs.get(slot).copied().unwrap_or(true)
    }
}

/// What one call site hands on, where what it hands on lands, and what it
/// yields.
///
/// Two questions are asked of a call site and they are not the same
/// question, so they are not the same answer.
///
/// MEMBERSHIP asks: does anything about THIS call still belong to a solve?
/// An argument the fixpoint is still solving puts the callee's matching slot
/// on the caller's cycle; a result it is still solving puts the callee's
/// whole return on it and names no slot at all. Both are facts about the one
/// value this site writes, so `enter(xs) -> cont(xs, [])` handing a literal
/// `[]` hands on nothing unsolved and stays outside the cycle it seeds.
///
/// KEYING asks: what coordinate does the SLOT this argument lands in get?
/// One slot gets one rule, so a seed call handing `[]` and an ascent call
/// handing `[x | acc]` must name the position alike or the seed keys apart
/// from every round after it. That answer is about the whole slot, folded
/// over every call site feeding it, and it is the same answer whichever of
/// them is being resolved.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct CallSiteUnknowns {
    /// One shape per positional argument: where unknown-ness sits inside the
    /// value THIS site hands on.
    pub(crate) arguments: Vec<KeyShape>,
    /// One shape per positional argument: where unknown-ness sits inside
    /// everything that ARRIVES at the slot that argument lands in, this
    /// site's own value among it. It is published by the caller because only
    /// a caller has the reach to compute it -- a callee like `wrap(v)`
    /// reaches nothing and can say nothing about the climbing value its
    /// caller hands it. An argument that lands in no named slot, because the
    /// call is made through a value, answers for itself.
    pub(crate) destinations: Vec<KeyShape>,
    /// What this site yields is itself a position the fixpoint is solving.
    pub(crate) result: bool,
}

impl CallSiteUnknowns {
    /// Nothing about this call belongs to a solve.
    pub(crate) fn is_settled(&self) -> bool {
        !self.result && self.arguments.iter().all(KeyShape::is_settled)
    }
}

/// Where unknown-ness sits inside one argument, and therefore where its key
/// coordinate stops being what the walk observed.
///
/// Structure the skeleton exposes survives: an accumulator built by consing
/// an unsolved value onto a solved list is `List(Unknown)`, and keys as a
/// list of the variable at its element address, because only the element is
/// still climbing.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum KeyShape {
    /// The fixpoint has settled everything here: key on what arrived.
    #[default]
    Settled,
    /// A position the fixpoint is still solving: key on its address.
    Unknown,
    Tuple(Vec<KeyShape>),
    List(Box<KeyShape>),
    Map(Vec<(MapKey, KeyShape)>),
}

impl KeyShape {
    pub(crate) fn is_settled(&self) -> bool {
        matches!(self, KeyShape::Settled)
    }

    /// Join two alternatives of one argument. `Settled` is the identity: a
    /// path that settles everything constrains nothing, so what the other
    /// path is still solving decides. Two different constructors cannot be
    /// walked together, so their join is the whole position -- naming more
    /// than a round needs costs an address variable where a concrete key
    /// would also have worked, and never costs termination.
    pub(crate) fn join(self, other: KeyShape) -> KeyShape {
        match (self, other) {
            (KeyShape::Settled, shape) | (shape, KeyShape::Settled) => shape,
            (KeyShape::Tuple(left), KeyShape::Tuple(right)) if left.len() == right.len() => KeyShape::Tuple(
                left.into_iter()
                    .zip(right)
                    .map(|(left, right)| left.join(right))
                    .collect(),
            ),
            (KeyShape::List(left), KeyShape::List(right)) => KeyShape::List(Box::new(left.join(*right))),
            (KeyShape::Map(left), KeyShape::Map(right))
                if left.len() == right.len()
                    && left.iter().zip(&right).all(|((left, _), (right, _))| left == right) =>
            {
                KeyShape::Map(
                    left.into_iter()
                        .zip(right)
                        .map(|((key, left), (_, right))| (key, left.join(right)))
                        .collect(),
                )
            }
            _ => KeyShape::Unknown,
        }
    }

    /// The activation-key coordinate a value of type `observed` deserves at
    /// structural address `path`. This is the one function that answers the
    /// keying question.
    ///
    /// A position the fixpoint has settled keys on what the walk observed
    /// there: that is ordinary specialization, and dispatch needs it. A
    /// position the fixpoint is still solving is an ITERATE -- what the walk
    /// observed is how far the ascent has climbed, not what the program
    /// denotes -- so it is named by the variable that addresses it instead.
    /// That is the same coordinate at every round, so the callee has ONE
    /// activation whose input evidence simply grows to the solved type. The
    /// precise evidence is untouched and still reaches the callee through
    /// `ActivationInputs`: this is the ordinary key-is-not-evidence split,
    /// one axis over.
    pub(crate) fn coordinate(&self, types: &mut Types, observed: Ty, path: &mut Vec<AddrStep>) -> Ty {
        match self {
            KeyShape::Settled => observed,
            KeyShape::Unknown => types.address_var(path),
            KeyShape::Tuple(elems) => {
                let elems = elems
                    .iter()
                    .enumerate()
                    .map(|(index, elem)| {
                        elem.child(
                            types,
                            observed,
                            ProjectStep::TupleField(index),
                            AddrStep::Field(index as u16),
                            path,
                        )
                    })
                    .collect::<Vec<_>>();
                types.tuple(&elems)
            }
            KeyShape::List(elem) => {
                let elem = elem.child(types, observed, ProjectStep::ListElement, AddrStep::Elem, path);
                types.list(elem)
            }
            KeyShape::Map(fields) => {
                let fields = fields
                    .iter()
                    .enumerate()
                    .map(|(index, (key, value))| {
                        let coordinate = value.child(
                            types,
                            observed,
                            ProjectStep::MapField(key.clone()),
                            AddrStep::MapField(index as u16),
                            path,
                        );
                        (key.clone(), coordinate)
                    })
                    .collect::<Vec<_>>();
                types.map(&fields)
            }
        }
    }

    fn child(
        &self,
        types: &mut Types,
        observed: Ty,
        step: ProjectStep,
        address: AddrStep,
        path: &mut Vec<AddrStep>,
    ) -> Ty {
        let observed = step.apply(types, observed);
        path.push(address);
        let coordinate = self.coordinate(types, observed, path);
        path.pop();
        coordinate
    }
}

/// The graph of static positions, with each edge labelled by whether it
/// crosses a constructor.
struct PositionGraph<'a> {
    skeletons: &'a HashMap<FunctionId, Rc<FunctionSkeleton>>,
    /// Every argument handed to one callee slot, in the caller's vocabulary.
    slot_feeds: HashMap<(FunctionId, usize), Vec<(FunctionId, Skeleton)>>,
    index: HashMap<Position, usize>,
    nodes: Vec<Position>,
    /// `branches[n]` holds each alternative `n` denotes, in the vocabulary of
    /// the function that wrote it, paired with whether it is `n`'s OWN --
    /// produced by `n`'s equation without crossing a bare edge. A branch
    /// absorbed from a neighbour is carried (the flattening needs it, and so
    /// does the next absorber) but it is not `n`'s own, so the constructor in
    /// it guards an edge out of the neighbour that built it, never one out
    /// of `n`.
    branches: Vec<Vec<(FunctionId, Skeleton, bool)>>,
    /// `edges[n]` holds `(target, guarded)` for every position `n` depends on.
    edges: Vec<Vec<(usize, bool)>>,
}

impl<'a> PositionGraph<'a> {
    fn new(skeletons: &'a HashMap<FunctionId, Rc<FunctionSkeleton>>) -> Self {
        let mut graph = Self {
            skeletons,
            slot_feeds: HashMap::new(),
            index: HashMap::new(),
            nodes: Vec::new(),
            branches: Vec::new(),
            edges: Vec::new(),
        };
        let mut callers: Vec<FunctionId> = skeletons.keys().copied().collect();
        callers.sort_by_key(|function| function.as_u32());
        for caller in callers {
            let callsites: Vec<CallSiteId> = skeletons[&caller].arguments.keys().copied().collect();
            for callsite in callsites {
                if let Some((callee, mode)) = graph.named_callee(caller, callsite) {
                    graph.feed_slots(caller, callsite, callee, mode);
                }
            }
        }
        graph
    }

    /// Records each of one call site's arguments as an alternative arriving
    /// at the callee slot it lands in.
    fn feed_slots(&mut self, caller: FunctionId, callsite: CallSiteId, callee: FunctionId, mode: CallInputMode) {
        let Some(arguments) = self.skeletons[&caller].arguments.get(&callsite).cloned() else {
            return;
        };
        let Some(callee_skeleton) = self.skeletons.get(&callee) else {
            return;
        };
        let input_len = callee_skeleton.input_len;
        for (index, argument) in arguments.iter().enumerate() {
            let Some(slot) = mode.semantic_index(input_len, arguments.len(), index) else {
                continue;
            };
            let feeds = self.slot_feeds.entry((callee, slot)).or_default();
            let feed = (caller, argument.clone());
            if !feeds.contains(&feed) {
                feeds.push(feed);
            }
        }
    }

    /// The function one of `function`'s call sites names, with how its
    /// positional arguments land. A call made through a value names none, so
    /// it reaches nothing here.
    fn named_callee(&self, function: FunctionId, callsite: CallSiteId) -> Option<(FunctionId, CallInputMode)> {
        self.skeletons.get(&function)?.callees.get(&callsite).copied()
    }

    /// Where each of one call site's positional arguments lands. A call made
    /// through a value names no callee, and a callee outside this reach has
    /// no slots to name, so in both cases an argument answers for itself.
    fn destinations(&self, caller: FunctionId, callsite: CallSiteId, arity: usize) -> Vec<Option<(FunctionId, usize)>> {
        let Some((callee, mode)) = self.named_callee(caller, callsite) else {
            return vec![None; arity];
        };
        let Some(callee_skeleton) = self.skeletons.get(&callee) else {
            return vec![None; arity];
        };
        let input_len = callee_skeleton.input_len;
        (0..arity)
            .map(|index| mode.semantic_index(input_len, arity, index).map(|slot| (callee, slot)))
            .collect()
    }

    /// Where unknown-ness sits inside everything that ARRIVES at one callee
    /// slot: the join over every call site this walk can see feeding it.
    ///
    /// One slot gets one coordinate rule, so a seed call handing `[]` and an
    /// ascent call handing `[x | acc]` are folded together here rather than
    /// each answering for the single value it happens to write. `Settled` is
    /// the join's identity, so a path that settles everything constrains
    /// nothing and what another path is still solving decides.
    ///
    /// Asking this from the CALLER is what makes the answer available at
    /// all. A caller's reach contains the callee's, and on top of that it
    /// contains the argument it writes itself -- the one contribution a
    /// callee like `wrap(v)`, which reaches nothing, can never see.
    fn slot_shape(&self, unknown: &HashSet<Position>, callee: FunctionId, slot: usize) -> KeyShape {
        self.slot_feeds
            .get(&(callee, slot))
            .into_iter()
            .flatten()
            .map(|(feeder, argument)| key_shape(unknown, *feeder, argument))
            .fold(KeyShape::Settled, KeyShape::join)
    }

    fn node(&mut self, position: Position) -> usize {
        if let Some(&existing) = self.index.get(&position) {
            return existing;
        }
        let index = self.nodes.len();
        self.index.insert(position.clone(), index);
        self.nodes.push(position);
        self.branches.push(Vec::new());
        self.edges.push(Vec::new());
        index
    }

    /// Grows every reachable node's branch set to the least fixed point of
    /// one pass over the node vector, repeated until nothing moves. A bare
    /// reference reads the referent NODE's current branches rather than
    /// descending into its equation, so a cycle of them converges instead of
    /// unfolding forever; branch sets only ever grow over a finite universe
    /// of subterms, so the rounds are finite.
    fn build(&mut self, seeds: Vec<Position>) {
        for seed in seeds {
            self.node(seed);
        }
        loop {
            let mut moved = false;
            let mut next = 0;
            while next < self.nodes.len() {
                let position = self.nodes[next].clone();
                for (function, branch, direct) in self.expand_node(&position) {
                    match self.branches[next]
                        .iter_mut()
                        .find(|(held_function, held, _)| *held_function == function && *held == branch)
                    {
                        // A branch that reaches a node both ways is its own:
                        // one path built it here, whatever the other did.
                        Some((_, _, held_direct)) if direct && !*held_direct => {
                            *held_direct = true;
                            moved = true;
                        }
                        Some(_) => {}
                        None => {
                            self.branches[next].push((function, branch, direct));
                            moved = true;
                        }
                    }
                }
                let position = self.nodes[next].clone();
                let children: Vec<Position> = self.branches[next]
                    .iter()
                    .filter(|(_, _, direct)| *direct)
                    .flat_map(|(function, branch, _)| {
                        guarded_positions(*function, branch)
                            .into_iter()
                            .filter(|child| !reconstructs(&position, *function, branch, child))
                            .collect::<Vec<_>>()
                    })
                    .collect();
                for child in children {
                    let target = self.node(child);
                    self.edge(next, target, true);
                }
                next += 1;
            }
            if !moved {
                break;
            }
        }
    }

    fn edge(&mut self, from: usize, to: usize, guarded: bool) {
        if !self.edges[from].contains(&(to, guarded)) {
            self.edges[from].push((to, guarded));
        }
    }

    /// One node's branch set, recomputed from its equation and the memo.
    /// Each alternative is paired with whether this node built it itself.
    fn expand_node(&mut self, position: &Position) -> Vec<(FunctionId, Skeleton, bool)> {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        let from = self.node(position.clone());
        match position {
            Position::Return(function) => {
                let Some(skeleton) = self.skeletons.get(function).cloned() else {
                    return out;
                };
                // A declared return states its own answer and guards
                // nothing, so it puts no branch on any cycle. The entries
                // stay apart in the skeleton; the static question is asked
                // of all of them at once, because which ones an activation
                // reaches is not a static fact.
                if let Returns::Entries(entries) = &skeleton.returns {
                    for entry in entries.values() {
                        self.expand_into(from, *function, entry, &mut out, &mut seen);
                    }
                }
            }
            Position::Slot(function, slot) => {
                let feeds = self.slot_feeds.get(&(*function, *slot)).cloned().unwrap_or_default();
                for (caller, argument) in feeds {
                    self.expand_into(from, caller, &argument, &mut out, &mut seen);
                }
            }
            Position::Result(function, callsite) => {
                // What a call site yields is what its callee returns: one
                // bare edge, and no shape of its own.
                if let Some((callee, _)) = self.named_callee(*function, *callsite) {
                    let target = self.node(Position::Return(callee));
                    self.edge(from, target, false);
                    for (branch_function, branch, _) in self.branches[target].clone() {
                        if seen.insert((branch_function, branch.clone())) {
                            out.push((branch_function, branch, false));
                        }
                    }
                }
            }
            Position::Interior(function, Skeleton::Project { of, step }) => {
                // A projection reads one layer out of whatever its subject
                // denotes. Reading through the subject's branches is a step
                // DOWN into subterms, never a further turn of the cycle the
                // subject sits on -- which is why a constructor a projection
                // immediately undoes leaves no guard behind.
                let mut inner = Vec::new();
                let mut inner_seen = HashSet::new();
                self.expand_into(from, *function, of, &mut inner, &mut inner_seen);
                for (branch_function, branch, _) in inner {
                    let projected = Skeleton::project(branch, step.clone());
                    self.expand_into(from, branch_function, &projected, &mut out, &mut seen);
                }
            }
            Position::Interior(_, _) => {}
        }
        out
    }

    /// Which of `function`'s input slots its own return is built from.
    ///
    /// A return is built from a slot when the slot's position is reachable
    /// from `Return(function)` over the graph's edges. Both edge kinds count:
    /// a bare edge means the return IS that position or a projection of it,
    /// and a guarded edge means it is wrapped inside a constructor the return
    /// hands out. Reaching the slot either way means a caller can read the
    /// value back, so its type is observable and the key must keep it.
    ///
    /// Composition across call sites needs no second walk. `Return(f)` reaches
    /// `Result(f, cs)`, which reaches `Return(g)`, which reaches `Slot(g, t)`,
    /// whose feeds carry `f`'s own argument skeleton and therefore reach
    /// `Slot(f, s)`. A slot another caller of `g` feeds is reached too, which
    /// keeps a slot verbatim that a narrower answer could have addressed --
    /// over-reading here costs a key, never a wrong one.
    fn reached_from_return(&mut self, function: FunctionId, input_len: usize) -> Box<[bool]> {
        let start = self.node(Position::Return(function));
        let mut seen = vec![false; self.nodes.len()];
        let mut frontier = vec![start];
        seen[start] = true;
        while let Some(node) = frontier.pop() {
            for (target, _) in self.edges[node].clone() {
                if !seen[target] {
                    seen[target] = true;
                    frontier.push(target);
                }
            }
        }
        (0..input_len)
            .map(|slot| {
                self.index
                    .get(&Position::Slot(function, slot))
                    .is_some_and(|node| seen[*node])
            })
            .collect()
    }

    /// Adds what `skeleton` denotes to `out`: a constructor is itself a
    /// branch, a union contributes each alternative, and a bare reference
    /// contributes its referent node's current branches -- recording a bare
    /// edge as it goes.
    fn expand_into(
        &mut self,
        from: usize,
        function: FunctionId,
        skeleton: &Skeleton,
        out: &mut Vec<(FunctionId, Skeleton, bool)>,
        seen: &mut HashSet<(FunctionId, Skeleton)>,
    ) {
        match skeleton {
            Skeleton::Bottom | Skeleton::Ground(_) => {}
            Skeleton::Union(branches) => {
                for branch in branches.clone() {
                    self.expand_into(from, function, &branch, out, seen);
                }
            }
            // A bare reference carries no shape of its own: what it denotes
            // is what the position it names denotes, so its branches are
            // absorbed and the edge is recorded as unguarded.
            Skeleton::Input(_) | Skeleton::Result { .. } | Skeleton::Project { .. } => {
                let Some(position) = position_of(function, skeleton) else {
                    return;
                };
                let target = self.node(position);
                self.edge(from, target, false);
                for (branch_function, branch, _) in self.branches[target].clone() {
                    if seen.insert((branch_function, branch.clone())) {
                        out.push((branch_function, branch, false));
                    }
                }
            }
            // A constructor is a whole body in its own right.
            other => {
                if seen.insert((function, other.clone())) {
                    out.push((function, other.clone(), true));
                }
            }
        }
    }
}

/// Derives what `function` needs to know to key its own calls, from the
/// skeletons of everything it can reach.
pub(crate) fn derive(skeletons: &HashMap<FunctionId, Rc<FunctionSkeleton>>, function: FunctionId) -> FunctionUnknowns {
    let Some(skeleton) = skeletons.get(&function).cloned() else {
        return FunctionUnknowns::default();
    };
    let mut graph = PositionGraph::new(skeletons);
    // The slot each argument lands in is a position this answer has to be
    // able to ask about, and expanding it is what brings the other call
    // sites feeding it into the walk. Seeding can only add positions the
    // walk had not reached: a position reached both ways was already a node,
    // so nothing the graph already said about `function` moves because of
    // it.
    let destinations: BTreeMap<CallSiteId, Vec<Option<(FunctionId, usize)>>> = skeleton
        .arguments
        .iter()
        .map(|(callsite, arguments)| (*callsite, graph.destinations(function, *callsite, arguments.len())))
        .collect();
    let mut seeds = vec![Position::Return(function)];
    seeds.extend((0..skeleton.input_len).map(|slot| Position::Slot(function, slot)));
    seeds.extend(
        skeleton
            .arguments
            .keys()
            .map(|callsite| Position::Result(function, *callsite)),
    );
    seeds.extend(
        destinations
            .values()
            .flatten()
            .flatten()
            .map(|(callee, slot)| Position::Slot(*callee, *slot)),
    );
    graph.build(seeds);

    let components = super::scc::strongly_connected_components((0..graph.nodes.len()).collect::<Vec<_>>(), |node| {
        graph.edges[*node].iter().map(|(target, _)| *target).collect::<Vec<_>>()
    });
    let mut unknown: HashSet<Position> = HashSet::new();
    for members in components {
        let nodes: HashSet<usize> = members.iter().copied().collect();
        // A cycle whose every edge is an alias or a projection has a
        // solution fixed by what enters it from outside, so it names nothing
        // anyone has to solve for.
        let productive = members.iter().any(|node| {
            graph.edges[*node]
                .iter()
                .any(|(target, guarded)| *guarded && nodes.contains(target))
        });
        if !productive {
            continue;
        }
        unknown.extend(members.iter().map(|node| graph.nodes[*node].clone()));
    }

    let callsites = skeleton
        .arguments
        .iter()
        .map(|(callsite, arguments)| {
            let site = CallSiteUnknowns {
                arguments: arguments
                    .iter()
                    .map(|argument| key_shape(&unknown, function, argument))
                    .collect(),
                destinations: arguments
                    .iter()
                    .zip(&destinations[callsite])
                    .map(|(argument, destination)| match destination {
                        // A named slot is answered for as a whole, this
                        // body's own argument among its feeders.
                        Some((callee, slot)) => graph.slot_shape(&unknown, *callee, *slot),
                        // Nothing here names a slot, so the value handed
                        // over answers for itself.
                        None => key_shape(&unknown, function, argument),
                    })
                    .collect(),
                result: unknown.contains(&Position::Result(function, *callsite)),
            };
            (callsite.as_u32(), site)
        })
        .collect();
    FunctionUnknowns {
        returns: unknown.contains(&Position::Return(function)),
        returned_inputs: graph.reached_from_return(function, skeleton.input_len),
        callsites,
    }
}

/// Where unknown-ness sits inside one skeleton: a constructor asks its
/// children, and a reference asks whether the position it names is one the
/// fixpoint is still solving. The answer does not descend into what a
/// reference reads -- field 2 of a parser's `{:ok, value, rest}` is a settled
/// token list however unsettled the tuple it is read out of.
fn key_shape(unknown: &HashSet<Position>, function: FunctionId, skeleton: &Skeleton) -> KeyShape {
    match skeleton {
        Skeleton::Bottom | Skeleton::Ground(_) => KeyShape::Settled,
        Skeleton::Union(branches) => branches
            .iter()
            .map(|branch| key_shape(unknown, function, branch))
            .fold(KeyShape::Settled, KeyShape::join),
        Skeleton::Tuple(elems) => {
            let shapes = elems
                .iter()
                .map(|elem| key_shape(unknown, function, elem))
                .collect::<Vec<_>>();
            settle(shapes.iter().all(KeyShape::is_settled), KeyShape::Tuple(shapes))
        }
        Skeleton::List { element, .. } => {
            let shape = key_shape(unknown, function, element);
            settle(shape.is_settled(), KeyShape::List(Box::new(shape)))
        }
        Skeleton::Map(fields) | Skeleton::Struct(_, fields) => {
            let shapes = fields
                .iter()
                .map(|(key, value)| (key.clone(), key_shape(unknown, function, value)))
                .collect::<Vec<_>>();
            settle(
                shapes.iter().all(|(_, shape)| shape.is_settled()),
                KeyShape::Map(shapes),
            )
        }
        Skeleton::Input(_) | Skeleton::Result { .. } | Skeleton::Project { .. } => {
            match position_of(function, skeleton).is_some_and(|position| unknown.contains(&position)) {
                true => KeyShape::Unknown,
                false => KeyShape::Settled,
            }
        }
    }
}

fn settle(everything_settled: bool, shape: KeyShape) -> KeyShape {
    match everything_settled {
        true => KeyShape::Settled,
        false => shape,
    }
}

#[cfg(test)]
#[path = "return_unknowns_test.rs"]
mod return_unknowns_test;
