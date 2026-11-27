//! Recursive types: a type that names itself where it repeats.
//!
//! `T = nil | {int, T, T}` is a binary tree of ints. It is stored as an
//! ordinary [`Ty`] whose descriptor names `T` itself as a child, so every
//! walker that reads a descriptor reads a recursive type the way it reads any
//! other, and only a walker that follows children to the bottom has to know
//! that the bottom can be where it started.
//!
//! # Meaning
//!
//! A value is finite, so a recursive type denotes the LEAST solution of its
//! equations: the values built by unfolding them a finite number of times.
//! `X = {int, X}` has no way out and denotes nothing; it commits as `none`.
//!
//! # Writing one
//!
//! [`Types::recursive`] hands the caller one binder variable per equation.
//! The caller builds each right-hand side as an ordinary type that mentions the
//! binders, and the commit solves the system. Until then a binder is a type
//! variable like any other, so building the bodies needs no new machinery.
//!
//! # One meaning, one id
//!
//! The commit puts the equation graph in a normal form before it hands out
//! ids: it inlines a binder that stands alone in a union (`X = X | A` is
//! `X = A`), drops what is empty, absorbs clauses another clause covers, and
//! merges nodes that unfold alike (partition refinement). Each strongly
//! connected group of what remains is one cluster, keyed by its bodies with
//! the members renamed to canonical variables in an order computed from the
//! bodies themselves. The same equations, written in any order and with any
//! redundant clause, reach the same key and so the same ids.
//!
//! A member's descriptor is indexed like any other, so writing out one
//! unfolding (`nil | {int, T, T}`) interns to `T` itself.
//!
//! # Deciding questions about one
//!
//! Emptiness and containment walk children, and below a recursive type a walk
//! can come back to a question it is already deciding. Such a question is
//! assumed to hold (`Recursion::assume`): a counterexample is a finite value,
//! so it is found at finite depth without the assumption. Assumptions live
//! only on the stack of questions being decided. An answer whose walk never
//! came back to a question opened outside it used no assumption, so it is the
//! answer of the type itself and is kept until the root question finishes;
//! an answer that did come back is never kept, so an assumption never
//! outlives the question it served.
//!
//! A set operation on recursive operands can likewise arrive back at itself.
//! The operation in flight answers its own re-entry with a fresh binder, and
//! the result that mentions the binder is committed as a recursive type
//! (`Types::recursive_operation`).
//!
//! # The residual
//!
//! Normalization steps that fuse tuple rectangles or do list arithmetic treat
//! a member as an opaque coordinate, so a spelling that only those steps
//! would recognise can still get a second id for one meaning.

use std::cell::RefCell;
use std::cmp::Ordering;

use crate::fast_hash::{HashMap, HashSet};

use super::attrs::{self, TyAttrs};
use super::axis;
use super::descr::Descr;
use super::order::ClauseOrder;
use super::{BinaryTypeOperation, Ty, TyCtx, TypeVarId, Types};

/// The tag of a binder variable: a placeholder for a member of a recursive
/// type while its equations are written or solved. Below the structural
/// address tag, and above every closure-surface variable.
pub(super) const BINDER_TAG: u32 = 0x4000_0000;
/// The binders that name the members of a cluster in its key, numbered in the
/// cluster's canonical order.
const CANON_TAG: u32 = BINDER_TAG | 0x2000_0000;
/// Child ids from here up name a node of the equation graph being solved, not
/// an interned type. The arena never reaches them.
const NODE_BASE: u32 = 0xF000_0000;

/// The recursive types a world knows, and the questions being decided about
/// them.
#[derive(Default)]
pub(super) struct Recursion {
    /// Whether any recursive type exists or is being solved. Until one does,
    /// no question pays for the cycle check.
    active: bool,
    members: HashMap<Ty, Member>,
    clusters: Vec<Cluster>,
    by_key: HashMap<Vec<Descr>, usize>,
    /// The questions being decided, each with its depth on the stack.
    questions: RefCell<HashMap<Question, usize>>,
    /// Answers, within the top-level question being decided, that no
    /// assumption outside their own subtree fed; dropped when it finishes.
    closed_answers: RefCell<HashMap<Question, bool>>,
    /// The shallowest open question the walk since the current question began
    /// arrived back at.
    shallowest_return: std::cell::Cell<usize>,
    /// How many questions have been asked, answered or not.
    pub(super) asked: std::cell::Cell<u64>,
    next_binder: u32,
    /// The constructions in flight over recursive types, each with the
    /// binder that answers a re-entry.
    open: Vec<(Open, Ty)>,
    /// What each operation binder stands for, once its operation finished but
    /// its result still mentioned an operation further out.
    pending: HashMap<TypeVarId, Ty>,
    /// The equation graphs being normalised, innermost last.
    pub(super) windows: Vec<Window>,
}

/// The nodes of one equation graph while it is normalised: unindexed arena
/// slots that exist for the walk, found by descriptor so that a descriptor
/// naming a node is minted once.
#[derive(Default)]
pub(super) struct Window {
    nodes: Vec<Ty>,
    by_descr: HashMap<Descr, Ty>,
}

/// An equation graph: node descriptors, children naming nodes as
/// `NODE_BASE + n`, and the node each binder stands for.
#[derive(Clone, PartialEq)]
struct System {
    nodes: Vec<Descr>,
    roots: Vec<usize>,
}

/// A graph that needs more rounds than this has not reached a fixpoint.
const MAX_ROUNDS: usize = 8;

#[derive(Clone, Copy)]
struct Member {
    cluster: usize,
    index: usize,
}

struct Cluster {
    /// Each member's descriptor with the members renamed to canonical
    /// binders, in canonical order.
    key: Vec<Descr>,
    members: Vec<Ty>,
}

/// A construction over recursive types that can arrive back at itself: a set
/// operation, or the interning of a descriptor whose normalization interns
/// its coordinates.
#[derive(Clone, PartialEq)]
pub(super) enum Open {
    Operation(BinaryTypeOperation),
    Intern(Box<Descr>),
    Map(Mapper, Ty),
}

/// A reading of a type as a type. One that maps a type by mapping its
/// children arrives, on a recursive type, back at the member it is mapping,
/// and the in-flight protocol makes the result a recursive type too.
#[derive(Clone, PartialEq)]
pub(super) enum Mapper {
    ValueLane,
    StructuralSurface,
    RuntimeReading,
    WidenLiterals,
    EraseClosureIdentity,
    CanonicalClosureSurface,
    /// Under the lambdas whose captures the type sits inside.
    FoldSelfNestedClosures(Vec<crate::fz_ir::FnId>),
    Instantiate(super::Sigma<Ty>),
    /// A variable's address is its first occurrence, so a member met again
    /// below itself is addressed as it was the first time.
    Address(super::addressed::AddressOwner),
    RuntimeEnvelope(
        super::RuntimeEnvelopePolarity,
        super::RuntimeEnvelopePurpose,
        super::Sigma<Ty>,
    ),
}

/// A question emptiness or containment can arrive back at.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) enum Question {
    Empty(Descr),
    Subtype(Descr, Descr),
    Disjoint(Descr, Descr),
}

impl Recursion {
    /// The cluster key and position of a member of a recursive type.
    pub(super) fn member_key(&self, ty: Ty) -> Option<(&[Descr], usize)> {
        self.members
            .get(&ty)
            .map(|m| (self.clusters[m.cluster].key.as_slice(), m.index))
    }

    pub(super) fn is_member(&self, ty: Ty) -> bool {
        self.members.contains_key(&ty)
    }

    pub(super) fn active(&self) -> bool {
        self.active
    }

    /// Decide `question`, assuming it holds wherever deciding it arrives back
    /// at it.
    pub(super) fn assume(&self, question: Question, decide: impl FnOnce() -> bool) -> bool {
        self.asked.set(self.asked.get() + 1);
        if let Some(depth) = self.questions.borrow().get(&question).copied() {
            self.shallowest_return.set(self.shallowest_return.get().min(depth));
            return true;
        }
        if let Some(verdict) = self.closed_answers.borrow().get(&question).copied() {
            return verdict;
        }
        let depth = self.questions.borrow().len();
        self.questions.borrow_mut().insert(question.clone(), depth);
        let outer = self.shallowest_return.replace(usize::MAX);
        let verdict = decide();
        let returned = self.shallowest_return.replace(outer);
        self.questions.borrow_mut().remove(&question);
        if returned < depth {
            self.shallowest_return.set(outer.min(returned));
        } else {
            self.closed_answers.borrow_mut().insert(question, verdict);
        }
        if depth == 0 {
            self.closed_answers.borrow_mut().clear();
        }
        verdict
    }
}

impl TyCtx<'_> {
    /// Whether deciding a question about `d` can arrive back at itself.
    pub(super) fn reaches_recursion(&self, d: &Descr) -> bool {
        self.recursion.active() && d.children().any(|(child, _)| self.attrs(&child).recursive())
    }

    /// Whether the interned coordinate `t` is empty. An interned type other
    /// than `none` is inhabited, except a node of an equation still being
    /// solved, which only a walk can judge.
    pub(super) fn coordinate_empty(&self, t: &Ty) -> bool {
        let d = self.descr(t);
        if self.attrs(t).unsettled() {
            return d.is_empty(*self);
        }
        d.looks_empty()
    }
}

/// Recursive equations opened by [`Types::recursive_equations`]: one binder
/// per equation, each standing for that equation's solution while its
/// right-hand side is built. [`Types::solve_recursive`] consumes them.
pub struct RecursiveEquations {
    ids: Vec<TypeVarId>,
    binders: Vec<Ty>,
}

impl RecursiveEquations {
    pub fn binders(&self) -> &[Ty] {
        &self.binders
    }
}

impl Types {
    /// Whether `ty` is a member of a recursive type. A walk that follows a
    /// path stops here: the member is its own fixpoint, so it stands whole at
    /// the path where the walk entered it.
    pub(super) fn is_recursive_member(&self, ty: &Ty) -> bool {
        self.interner.recursion.is_member(*ty)
    }

    /// The recursive types `count` equations define. `write` receives one
    /// binder per equation and returns each right-hand side, built as an
    /// ordinary type that mentions the binders.
    pub fn recursive(&mut self, count: usize, write: impl FnOnce(&mut Types, &[Ty]) -> Vec<Ty>) -> Vec<Ty> {
        let equations = self.recursive_equations(count);
        let bodies = write(self, equations.binders());
        self.solve_recursive(equations, &bodies)
    }

    /// Opens `count` recursive equations, for a caller that builds their
    /// right-hand sides somewhere `recursive`'s closure cannot reach.
    pub fn recursive_equations(&mut self, count: usize) -> RecursiveEquations {
        let ids: Vec<TypeVarId> = (0..count).map(|_| self.mint_binder()).collect();
        let binders = ids.iter().map(|id| self.type_var(*id)).collect();
        RecursiveEquations { ids, binders }
    }

    /// The recursive types the opened `equations` define, given one
    /// right-hand side per binder.
    pub fn solve_recursive(&mut self, equations: RecursiveEquations, bodies: &[Ty]) -> Vec<Ty> {
        assert_eq!(
            bodies.len(),
            equations.ids.len(),
            "one right-hand side per recursive equation"
        );
        self.solve_equations(&equations.ids, bodies)
    }

    pub(super) fn mint_binder(&mut self) -> TypeVarId {
        let recursion = &mut self.interner.recursion;
        let id = recursion.next_binder;
        assert!(id < CANON_TAG - BINDER_TAG, "recursive binders exhausted");
        recursion.next_binder += 1;
        TypeVarId(BINDER_TAG | id)
    }

    /// Run a construction over recursive types. Arriving back at one in
    /// flight answers it with that construction's binder; the result that
    /// mentions the binder is the binder's right-hand side. Returns the
    /// result and whether it may be remembered: a result that still names a
    /// construction in flight stands for something unfinished.
    pub(super) fn recursive_operation(&mut self, key: Open, compute: impl FnOnce(&mut Self) -> Ty) -> (Ty, bool) {
        if let Some((_, binder)) = self.interner.recursion.open.iter().find(|(open, _)| *open == key) {
            return (*binder, false);
        }
        let id = self.mint_binder();
        let binder = self.type_var(id);
        self.interner.recursion.open.push((key, binder));
        let result = compute(self);
        let mut mentioned = self.mentioned_operation_binders(result);
        self.interner.recursion.open.pop();
        if mentioned.is_empty() {
            return (result, true);
        }
        mentioned.insert(id);
        self.interner.recursion.pending.insert(id, result);
        let open: Vec<TypeVarId> = self
            .interner
            .recursion
            .open
            .iter()
            .map(|(_, open)| self.single_var(*open))
            .collect();
        if open.iter().any(|id| mentioned.contains(id)) {
            return (binder, false);
        }
        let binders: Vec<TypeVarId> = mentioned.into_iter().collect();
        let bodies: Vec<Ty> = binders
            .iter()
            .map(|b| {
                self.interner
                    .recursion
                    .pending
                    .remove(b)
                    .expect("a finished operation's body")
            })
            .collect();
        let solved = self.solve_equations(&binders, &bodies);
        let at = binders
            .iter()
            .position(|b| *b == id)
            .expect("the operation's own binder");
        (solved[at], true)
    }

    /// `ty` mapped by `mapper`, through the in-flight protocol when `ty`
    /// reaches a recursive type. Returns the result and whether it may be
    /// remembered.
    /// `mapper` is called only for such a type, so a reading keyed by what it
    /// carries copies that only where it is needed.
    pub(super) fn map_type(
        &mut self,
        mapper: impl FnOnce() -> Mapper,
        ty: Ty,
        compute: impl FnOnce(&mut Self) -> Ty,
    ) -> (Ty, bool) {
        if !self.ctx().attrs(&ty).recursive() {
            return (compute(self), true);
        }
        self.recursive_operation(Open::Map(mapper(), ty), compute)
    }

    /// Every operation binder `result` mentions, through the bodies of the
    /// finished operations it names, in mint order.
    fn mentioned_operation_binders(&self, result: Ty) -> std::collections::BTreeSet<TypeVarId> {
        let mut found = std::collections::BTreeSet::new();
        let mut pending = vec![result];
        while let Some(ty) = pending.pop() {
            if !self.has_vars(&ty) {
                continue;
            }
            for id in self.free_var_ids(&ty) {
                if !self.is_operation_binder(id) || !found.insert(id) {
                    continue;
                }
                if let Some(body) = self.interner.recursion.pending.get(&id) {
                    pending.push(*body);
                }
            }
        }
        found
    }

    fn is_operation_binder(&self, id: TypeVarId) -> bool {
        let recursion = &self.interner.recursion;
        recursion.pending.contains_key(&id) || recursion.open.iter().any(|(_, open)| self.single_var(*open) == id)
    }

    fn single_var(&self, ty: Ty) -> TypeVarId {
        *self
            .descr(&ty)
            .vars
            .values
            .iter()
            .next()
            .expect("a binder type is one variable")
    }

    /// Solve the equations `binders[i] = bodies[i]` and commit the solution.
    pub(super) fn solve_equations(&mut self, binders: &[TypeVarId], bodies: &[Ty]) -> Vec<Ty> {
        self.interner.recursion.active = true;
        let nodes = self.equation_graph(binders, bodies);
        let system = self.minimise(System {
            nodes,
            roots: (0..binders.len()).collect(),
        });
        let (classes, _) = self.refine(&system.nodes);
        let resolved = self.resolve_classes(&system.nodes, &classes);
        system.roots.iter().map(|root| resolved[classes[*root]]).collect()
    }

    /// The system normalised and minimised until a round changes nothing.
    /// Each round reads only the previous round's graph.
    fn minimise(&mut self, system: System) -> System {
        let mut current = self.quotient(system);
        let mut history = vec![current.clone()];
        loop {
            let normalised = self.normalise_round(&current);
            let next = self.quotient(normalised);
            if next == current {
                return current;
            }
            assert!(
                !history.contains(&next),
                "the equations oscillate: a round returned to an earlier graph"
            );
            assert!(
                history.len() < MAX_ROUNDS,
                "the equations did not reach a fixpoint in {MAX_ROUNDS} rounds"
            );
            history.push(next.clone());
            current = next;
        }
    }

    /// One round: the nodes are placed in the arena, emptiness and absorption
    /// settle them, and each is put in normal form against the settled graph.
    /// A descriptor the normal form builds that names a node is minted as a
    /// node (`Types::intern`). Nodes are taken back unless something else was
    /// interned among them.
    fn normalise_round(&mut self, system: &System) -> System {
        let nodes = self.open_window(&system.nodes);
        self.settle_nodes(&nodes);
        let normalised: Vec<Descr> = nodes
            .iter()
            .map(|ty| {
                let d = self.descr(ty).clone();
                self.normal_form(d)
            })
            .collect();
        for (ty, d) in nodes.iter().zip(normalised) {
            self.interner.arena[ty.0 as usize] = d;
        }
        System {
            nodes: self.close_window(),
            roots: system.roots.clone(),
        }
    }

    /// One node per class, in class order, holding the class's canonical shape;
    /// what no root reaches is dropped.
    fn quotient(&mut self, system: System) -> System {
        let (classes, shapes) = self.refine(&system.nodes);
        let count = classes.iter().copied().max().map_or(0, |c| c + 1);
        let names: HashMap<Ty, usize> = (0..count as u32)
            .map(|c| (self.type_var(TypeVarId(CANON_TAG | c)), c as usize))
            .collect();
        let mut by_class: Vec<Option<Descr>> = vec![None; count];
        for (node, class) in classes.iter().enumerate() {
            by_class[*class].get_or_insert_with(|| {
                let mut d = shapes[node].clone();
                d.map_children(&mut |child, _| names.get(&child).map_or(child, |c| Ty(NODE_BASE + *c as u32)));
                d
            });
        }
        let by_class: Vec<Descr> = by_class
            .into_iter()
            .map(|d| d.expect("every class has a node"))
            .collect();
        let mut reached: Vec<usize> = Vec::new();
        let mut pending: Vec<usize> = system.roots.iter().map(|root| classes[*root]).collect();
        while let Some(class) = pending.pop() {
            if reached.contains(&class) {
                continue;
            }
            reached.push(class);
            pending.extend(
                by_class[class]
                    .children()
                    .filter(|(child, _)| child.0 >= NODE_BASE)
                    .map(|(child, _)| (child.0 - NODE_BASE) as usize),
            );
        }
        reached.sort_unstable();
        let renumber = |class: usize| reached.iter().position(|c| *c == class).expect("a reached class");
        let nodes = reached
            .iter()
            .map(|class| {
                let mut d = by_class[*class].clone();
                d.map_children(&mut |child, _| {
                    if child.0 >= NODE_BASE {
                        Ty(NODE_BASE + renumber((child.0 - NODE_BASE) as usize) as u32)
                    } else {
                        child
                    }
                });
                d
            })
            .collect();
        let roots = system.roots.iter().map(|root| renumber(classes[*root])).collect();
        System { nodes, roots }
    }

    /// The equations as a graph over descriptors. Node `i < binders.len()` is
    /// binder `i`; every other node is a child type that mentions a binder.
    /// A child naming node `n` is written `NODE_BASE + n`.
    fn equation_graph(&self, binders: &[TypeVarId], bodies: &[Ty]) -> Vec<Descr> {
        let solving: HashSet<TypeVarId> = binders.iter().copied().collect();
        let mentions = |ty: &Ty| self.has_vars(ty) && self.free_var_ids(ty).iter().any(|id| solving.contains(id));
        let mut nodes: Vec<Descr> = bodies.iter().map(|body| self.unfold(body, binders, bodies)).collect();
        let mut node_of: HashMap<Ty, usize> = HashMap::default();
        for (i, binder) in binders.iter().enumerate() {
            let var = self
                .interner
                .lookup_existing(&Descr::var(*binder))
                .expect("a binder handed out is interned");
            node_of.insert(var, i);
        }
        let mut next = 0;
        while next < nodes.len() {
            let children: Vec<Ty> = nodes[next].children().map(|(child, _)| child).collect();
            for child in children {
                if mentions(&child) && !node_of.contains_key(&child) {
                    node_of.insert(child, nodes.len());
                    nodes.push(self.unfold(&child, binders, bodies));
                }
            }
            next += 1;
        }
        for node in &mut nodes {
            node.map_children(&mut |child, _| match node_of.get(&child) {
                Some(n) => Ty(NODE_BASE + *n as u32),
                None => child,
            });
        }
        nodes
    }

    /// `ty`'s descriptor with every binder that stands alone in it replaced by
    /// that binder's right-hand side. A binder that reaches itself this way
    /// adds nothing: the least solution of `X = X | A` is `A`.
    fn unfold(&self, ty: &Ty, binders: &[TypeVarId], bodies: &[Ty]) -> Descr {
        let mut reached: Vec<usize> = Vec::new();
        let mut pending = vec![*ty];
        let mut out = Descr::none();
        while let Some(at) = pending.pop() {
            let mut d = self.descr(&at).clone();
            let named = strip_binders(&mut d, binders);
            out = out.union(self.ctx(), &d);
            for i in named {
                if !reached.contains(&i) {
                    reached.push(i);
                    pending.push(bodies[i]);
                }
            }
        }
        out
    }

    /// Places the graph's nodes in the arena unindexed, so emptiness,
    /// containment and normal form read the cycles, and opens the window that
    /// mints the nodes normal form builds.
    fn open_window(&mut self, graph: &[Descr]) -> Vec<Ty> {
        let base = self.interner.arena.len() as u32;
        let mut window = Window::default();
        for node in graph {
            let mut d = node.clone();
            d.map_children(&mut |child, _| {
                if child.0 >= NODE_BASE {
                    Ty(child.0 - NODE_BASE + base)
                } else {
                    child
                }
            });
            let attrs = node_attrs(&self.interner.attrs, &d, base);
            let ty = self.interner.push_unindexed(d.clone(), attrs);
            window.by_descr.entry(d).or_insert(ty);
            window.nodes.push(ty);
        }
        let nodes = window.nodes.clone();
        self.interner.recursion.windows.push(window);
        nodes
    }

    /// The node for a descriptor that names a node of the open graph: the one
    /// already holding it, else a new one. The descriptor is first put in the
    /// form every node is in (covered clauses absorbed, clauses ordered), so a
    /// built union that says what a node already says is that node. Nothing
    /// that names a node is interned.
    pub(super) fn mint(&mut self, d: Descr) -> Ty {
        let window = self
            .interner
            .recursion
            .windows
            .last()
            .expect("a node is named inside a window");
        if let Some(ty) = window.by_descr.get(&d) {
            return *ty;
        }
        let mut d = self.settled(d);
        self.clause_order().sort_axes(&mut d);
        let window = self.interner.recursion.windows.last().expect("a node is named inside a window");
        if let Some(ty) = window.nodes.iter().find(|ty| *self.descr(ty) == d) {
            return *ty;
        }
        let attrs = attrs::attrs_of(&self.interner.attrs, &d).with_recursion(true);
        let ty = self.interner.push_unindexed(d.clone(), attrs);
        let window = self.interner.recursion.windows.last_mut().expect("a window is open");
        window.by_descr.insert(d, ty);
        window.nodes.push(ty);
        ty
    }

    /// Whether `d` names a node of a graph being normalised.
    pub(super) fn names_node(&self, d: &Descr) -> bool {
        let recursion = &self.interner.recursion;
        !recursion.windows.is_empty()
            && d.children()
                .any(|(child, _)| self.interner.attrs[child.0 as usize].unsettled())
    }

    /// The graph the window holds, nodes written as `NODE_BASE + n`; the window
    /// is closed and its nodes taken back when nothing else was placed among
    /// them. Otherwise they stay in the arena, unindexed and named by nothing.
    fn close_window(&mut self) -> Vec<Descr> {
        let window = self.interner.recursion.windows.pop().expect("a window is open");
        let index: HashMap<Ty, usize> = window.nodes.iter().enumerate().map(|(n, ty)| (*ty, n)).collect();
        let graph = window
            .nodes
            .iter()
            .map(|ty| {
                let mut d = self.descr(ty).clone();
                d.map_children(&mut |child, _| index.get(&child).map_or(child, |n| Ty(NODE_BASE + *n as u32)));
                d
            })
            .collect();
        let first = window.nodes[0].0 as usize;
        if self.interner.arena.len() - first == window.nodes.len() {
            self.interner.truncate(first);
        }
        graph
    }

    /// The nodes with what is empty removed and what is covered absorbed.
    fn settle_nodes(&mut self, nodes: &[Ty]) {
        let empty: Vec<bool> = nodes
            .iter()
            .map(|ty| {
                let cx = self.ctx();
                cx.descr(ty).is_empty(cx)
            })
            .collect();
        let none = self.core.none;
        let position: HashMap<Ty, usize> = nodes.iter().enumerate().map(|(n, ty)| (*ty, n)).collect();
        for (ty, is_empty) in nodes.iter().zip(&empty) {
            let mut d = if *is_empty {
                Descr::none()
            } else {
                self.descr(ty).clone()
            };
            d.map_children(&mut |child, _| match position.get(&child) {
                Some(n) if empty[*n] => none,
                _ => child,
            });
            self.interner.arena[ty.0 as usize] = d;
        }
        for ty in nodes {
            let d = self.settled_node(*ty);
            self.interner.arena[ty.0 as usize] = d;
        }
    }

    /// One node with its empty clauses dropped and its covered clauses
    /// absorbed, every question walked rather than remembered: the node ids
    /// are about to be taken back.
    fn settled_node(&self, ty: Ty) -> Descr {
        self.settled(self.descr(&ty).clone())
    }

    /// `d` with its empty clauses dropped and its covered clauses absorbed.
    fn settled(&self, mut d: Descr) -> Descr {
        let cx = self.ctx();
        let none = self.core.none;
        axis::drop_empty_clauses(cx, &mut d, &|coordinate| *coordinate == none);
        let subtype = &|narrower: &Ty, wider: &Ty| cx.descr(narrower).is_subtype(cx, cx.descr(wider));
        let covers = &|wider: &Descr, narrower: &Descr| narrower.is_subtype(cx, wider);
        axis::absorb_axis(cx, &mut d.tuples, subtype, covers, &axis::TUPLES);
        axis::absorb_axis(cx, &mut d.lists, subtype, covers, &axis::LISTS);
        axis::absorb_axis(cx, &mut d.resources, subtype, covers, &axis::RESOURCES);
        axis::absorb_axis(cx, &mut d.maps, subtype, covers, &axis::MAPS);
        if d.looks_empty() {
            return Descr::none();
        }
        d
    }

    /// Partition refinement: the coarsest partition of `nodes` in which two
    /// nodes share a class only when their descriptors agree once every node
    /// they name is replaced by its class. Classes are numbered by sorting
    /// their descriptors, so the numbering depends on what the nodes say and
    /// not on the order they were given in. Returns each node's class and
    /// each node's descriptor in class terms.
    fn refine(&mut self, nodes: &[Descr]) -> (Vec<usize>, Vec<Descr>) {
        let mut classes = vec![0; nodes.len()];
        let mut count = usize::from(!nodes.is_empty());
        loop {
            let names: Vec<Ty> = (0..count as u32)
                .map(|c| self.type_var(TypeVarId(CANON_TAG | c)))
                .collect();
            let shapes: Vec<Descr> = nodes
                .iter()
                .map(|node| {
                    let mut d = node.clone();
                    d.map_children(&mut |child, _| {
                        if child.0 >= NODE_BASE {
                            names[classes[(child.0 - NODE_BASE) as usize]]
                        } else {
                            child
                        }
                    });
                    self.clause_order().sort_axes(&mut d);
                    d
                })
                .collect();
            let order = self.clause_order();
            let mut ranked: Vec<usize> = (0..nodes.len()).collect();
            ranked.sort_by(|&a, &b| {
                classes[a]
                    .cmp(&classes[b])
                    .then_with(|| order.cmp_descr(&shapes[a], &shapes[b]))
            });
            let mut next = vec![0; nodes.len()];
            let mut rank = 0;
            for (at, node) in ranked.iter().enumerate() {
                if at > 0 {
                    let before = ranked[at - 1];
                    if classes[before] != classes[*node] || shapes[before] != shapes[*node] {
                        rank += 1;
                    }
                }
                next[*node] = rank;
            }
            let next_count = if nodes.is_empty() { 0 } else { rank + 1 };
            let stable = next_count == count;
            classes = next;
            count = next_count;
            if stable {
                return (classes, shapes);
            }
        }
    }

    /// The type each class denotes. Classes are resolved one strongly
    /// connected group at a time, sinks first: a group with no cycle is an
    /// ordinary type over types already resolved, and a group with one is a
    /// cluster.
    fn resolve_classes(&mut self, graph: &[Descr], classes: &[usize]) -> Vec<Ty> {
        let count = classes.iter().copied().max().map_or(0, |c| c + 1);
        let mut representative = vec![usize::MAX; count];
        for (node, class) in classes.iter().enumerate().rev() {
            representative[*class] = node;
        }
        let edges: Vec<Vec<usize>> = representative
            .iter()
            .map(|node| {
                graph[*node]
                    .children()
                    .filter(|(child, _)| child.0 >= NODE_BASE)
                    .map(|(child, _)| classes[(child.0 - NODE_BASE) as usize])
                    .collect()
            })
            .collect();
        let mut resolved: Vec<Option<Ty>> = vec![None; count];
        for group in strongly_connected(&edges) {
            let cyclic = group.len() > 1 || edges[group[0]].contains(&group[0]);
            let rewrite = |child: Ty, resolved: &[Option<Ty>], local: &dyn Fn(usize) -> Option<usize>| {
                if child.0 < NODE_BASE {
                    return child;
                }
                let class = classes[(child.0 - NODE_BASE) as usize];
                match local(class) {
                    Some(at) => Ty(NODE_BASE + at as u32),
                    None => resolved[class].expect("a group's successors are resolved first"),
                }
            };
            if !cyclic {
                let class = group[0];
                let mut d = graph[representative[class]].clone();
                d.map_children(&mut |child, _| rewrite(child, &resolved, &|_| None));
                resolved[class] = Some(self.intern(d));
                continue;
            }
            let local = |class: usize| group.iter().position(|c| *c == class);
            let members: Vec<Descr> = group
                .iter()
                .map(|class| {
                    let mut d = graph[representative[*class]].clone();
                    d.map_children(&mut |child, _| rewrite(child, &resolved, &local));
                    d
                })
                .collect();
            let tys = self.commit_cluster(&members);
            for (at, class) in group.iter().enumerate() {
                resolved[*class] = Some(tys[at]);
            }
        }
        resolved
            .into_iter()
            .map(|ty| ty.expect("every class resolved"))
            .collect()
    }

    /// The ids of one cluster, `members` naming each other as nodes. The
    /// members are put in canonical order first, so an isomorphic cluster
    /// built before is found by its key.
    fn commit_cluster(&mut self, members: &[Descr]) -> Vec<Ty> {
        let (order, shapes) = self.refine(members);
        let count = order.iter().copied().max().map_or(0, |c| c + 1);
        let mut key: Vec<Option<Descr>> = vec![None; count];
        for (at, class) in order.iter().enumerate() {
            key[*class].get_or_insert_with(|| shapes[at].clone());
        }
        let key: Vec<Descr> = key.into_iter().map(|d| d.expect("every class has a member")).collect();
        let found = self.interner.recursion.by_key.get(&key).copied();
        let ids = match found {
            Some(cluster) => self.interner.recursion.clusters[cluster].members.clone(),
            None => self.add_cluster(key),
        };
        order.iter().map(|class| ids[*class]).collect()
    }

    fn add_cluster(&mut self, key: Vec<Descr>) -> Vec<Ty> {
        let names: HashMap<Ty, usize> = (0..key.len() as u32)
            .map(|c| (self.type_var(TypeVarId(CANON_TAG | c)), c as usize))
            .collect();
        let base = self.interner.arena.len() as u32;
        let ids: Vec<Ty> = (0..key.len() as u32).map(|at| Ty(base + at)).collect();
        let cluster = self.interner.recursion.clusters.len();
        for (index, id) in ids.iter().enumerate() {
            self.interner.recursion.members.insert(*id, Member { cluster, index });
        }
        let descrs: Vec<Descr> = key
            .iter()
            .map(|shape| {
                let mut d = shape.clone();
                d.map_children(&mut |child, _| names.get(&child).map_or(child, |at| ids[*at]));
                d
            })
            .collect();
        self.interner.recursion.by_key.insert(key.clone(), cluster);
        self.interner.recursion.clusters.push(Cluster {
            key,
            members: ids.clone(),
        });
        for d in descrs {
            self.interner
                .push_unindexed(d, TyAttrs::default().with_recursion(false));
        }
        self.assert_cycles_stay_in_cluster(&ids, base);
        self.settle_member_attrs(&ids);
        for id in &ids {
            self.interner.index_existing(*id);
        }
        ids
    }

    /// No type built while the members were normalised may sit on a cycle
    /// through them: walkers stop at members, so a cycle through any other
    /// type is never guarded. Types below `base` predate the members and
    /// cannot reach them.
    fn assert_cycles_stay_in_cluster(&self, ids: &[Ty], base: u32) {
        for member in ids {
            let mut seen = HashSet::default();
            let mut stack: Vec<Ty> = self.outside_children(member, ids);
            while let Some(ty) = stack.pop() {
                if ty.0 < base || ty.0 >= NODE_BASE || !seen.insert(ty) {
                    continue;
                }
                if let Some(back) = self
                    .descr(&ty)
                    .children()
                    .map(|(child, _)| child)
                    .find(|c| ids.contains(c))
                {
                    panic!(
                        "a recursive type's member {} reaches itself through {}, which is not a member and names {}",
                        self.display(member),
                        self.display(&ty),
                        self.display(&back),
                    );
                }
                stack.extend(self.outside_children(&ty, ids));
            }
        }
    }

    fn outside_children(&self, ty: &Ty, members: &[Ty]) -> Vec<Ty> {
        self.descr(ty)
            .children()
            .map(|(child, _)| child)
            .filter(|child| !members.contains(child))
            .collect()
    }

    /// Members name each other, so their attributes are the least fixpoint of
    /// the ordinary rule over the cluster.
    fn settle_member_attrs(&mut self, ids: &[Ty]) {
        loop {
            let next: Vec<TyAttrs> = ids
                .iter()
                .map(|id| {
                    let attrs = &self.interner.attrs;
                    attrs::attrs_from(self.descr(id), |child| attrs[child.0 as usize]).with_recursion(false)
                })
                .collect();
            let mut changed = false;
            for (id, attrs) in ids.iter().zip(next) {
                let slot = &mut self.interner.attrs[id.0 as usize];
                changed |= *slot != attrs;
                *slot = attrs;
            }
            if !changed {
                return;
            }
        }
    }
}

/// Remove the binders being solved from `d`'s variable axis, returning which.
fn strip_binders(d: &mut Descr, binders: &[TypeVarId]) -> Vec<usize> {
    assert!(
        !d.vars.cofinite || d.vars.values.is_empty(),
        "a recursive equation cannot negate its own binder"
    );
    let named: Vec<usize> = binders
        .iter()
        .enumerate()
        .filter(|(_, b)| d.vars.values.contains(b))
        .map(|(i, _)| i)
        .collect();
    d.vars.values.retain(|id| !binders.contains(id));
    named
}

/// The attributes of an unsettled node: its own facts, with every node it
/// names counted as recursive.
fn node_attrs(attrs: &[TyAttrs], d: &Descr, base: u32) -> TyAttrs {
    attrs::attrs_from(d, |child| {
        if child.0 >= base {
            TyAttrs::default().with_recursion(true)
        } else {
            attrs[child.0 as usize]
        }
    })
    .with_recursion(true)
}

/// The strongly connected components of `edges`, sinks first (Tarjan).
fn strongly_connected(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct Walk<'e> {
        edges: &'e [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        next: usize,
        groups: Vec<Vec<usize>>,
    }
    impl Walk<'_> {
        fn visit(&mut self, v: usize) {
            self.index[v] = Some(self.next);
            self.low[v] = self.next;
            self.next += 1;
            self.stack.push(v);
            self.on_stack[v] = true;
            for at in 0..self.edges[v].len() {
                let w = self.edges[v][at];
                match self.index[w] {
                    None => {
                        self.visit(w);
                        self.low[v] = self.low[v].min(self.low[w]);
                    }
                    Some(seen) if self.on_stack[w] => self.low[v] = self.low[v].min(seen),
                    Some(_) => {}
                }
            }
            if Some(self.low[v]) == self.index[v] {
                let mut group = Vec::new();
                loop {
                    let w = self.stack.pop().expect("v is on the stack");
                    self.on_stack[w] = false;
                    group.push(w);
                    if w == v {
                        break;
                    }
                }
                group.sort_unstable();
                self.groups.push(group);
            }
        }
    }
    let n = edges.len();
    let mut walk = Walk {
        edges,
        index: vec![None; n],
        low: vec![0; n],
        stack: Vec::new(),
        on_stack: vec![false; n],
        next: 0,
        groups: Vec::new(),
    };
    for v in 0..n {
        if walk.index[v].is_none() {
            walk.visit(v);
        }
    }
    walk.groups
}

/// Two members of different clusters compare by their cluster keys, two of
/// one cluster by position. Clusters are built from types that already exist,
/// so the keys of the clusters a key names are older, and the comparison
/// terminates.
pub(super) fn cmp_members(order: &ClauseOrder<'_>, a: (&[Descr], usize), b: (&[Descr], usize)) -> Ordering {
    let (a_key, a_at) = a;
    let (b_key, b_at) = b;
    a_key
        .len()
        .cmp(&b_key.len())
        .then_with(|| {
            a_key
                .iter()
                .zip(b_key)
                .map(|(x, y)| order.cmp_descr(x, y))
                .find(|o| *o != Ordering::Equal)
                .unwrap_or(Ordering::Equal)
        })
        .then_with(|| a_at.cmp(&b_at))
}

#[cfg(test)]
#[path = "recursive_test.rs"]
mod recursive_test;

#[cfg(test)]
#[path = "minimise_oscillation_test.rs"]
mod minimise_oscillation_test;

#[cfg(test)]
#[path = "minimise_questions_test.rs"]
mod minimise_questions_test;
