use std::collections::{BTreeSet, HashMap, VecDeque};

use super::axis;
use super::conj::Conj;
use super::descr::{DescrOf, StructureOf, canonical_brand_partition};
use super::emptiness::Operand;
use super::sigs::TupleSigOf;
use super::{
    BinaryTypeOperation, CallableSurfaceOps, TupleCoordinateOps, Ty, Types, normalize_literal_callable_surfaces_with,
    normalize_tuple_coordinate_difference_with,
};
use crate::fz_ir::FnId;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ComponentRef {
    Published(Ty),
    Local(NodeId),
}

impl ComponentRef {
    pub(crate) fn local(index: usize) -> Self {
        Self::Local(NodeId(index))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct NodeId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum RegularRef {
    Published(Ty),
    Local(usize),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct RegularKey {
    nodes: Vec<DescrOf<RegularRef>>,
}

/// Intern one strongly connected cluster, resolving it against the recursive
/// handles it mentions.
///
/// Minimizing the cluster on its own answers "which of my nodes are the same
/// state?" but not "is one of my states a handle that already exists?". So the
/// states of every mentioned handle join the refinement as fixed nodes, and a
/// mention becomes a reference to the fixed node rather than an opaque atom. A
/// class that lands with a fixed node is that handle -- fixed nodes are
/// already minimal, so a local can only join one by being bisimilar to it.
/// What is left over is the genuinely new part of the cluster: it alone is
/// keyed and minted, naming the resolved handles as ordinary children.
pub(super) fn intern(
    types: &mut Types,
    count: usize,
    build: impl FnOnce(&[ComponentRef]) -> Vec<DescrOf<ComponentRef>>,
) -> Vec<Ty> {
    assert!(count > 0, "a regular component needs at least one node");
    let nodes = (0..count)
        .map(|index| ComponentRef::Local(NodeId(index)))
        .collect::<Vec<_>>();
    let bodies = build(&nodes);
    assert_eq!(bodies.len(), count, "a regular component needs one body per node");
    assert_strongly_connected(&bodies);

    let handles = mentioned_handle_states(types, &bodies);
    let nodes = bodies_with_handle_states(types, bodies, &handles);
    let classes = refine_partition(types, &nodes);
    let class_count = classes.iter().copied().max().map_or(0, |class| class + 1);
    let resolved = resolved_classes(&classes, count, &handles, class_count);
    let handle_of = |node: usize| resolved[classes[node]];
    if (0..count).all(|node| handle_of(node).is_some()) {
        return (0..count)
            .map(|node| handle_of(node).expect("every node resolved to a handle"))
            .collect();
    }

    let class_bodies = quotient_bodies(types, &nodes, &classes, class_count);
    let residual = (0..class_count)
        .filter(|class| resolved[*class].is_none())
        .collect::<Vec<_>>();
    let mut residual_index = vec![None; class_count];
    for (index, &class) in residual.iter().enumerate() {
        residual_index[class] = Some(index);
    }
    let residual_bodies = residual
        .iter()
        .map(|&class| {
            let body = class_bodies[class].clone().map_children(|reference| match reference {
                RegularRef::Published(ty) => RegularRef::Published(ty),
                RegularRef::Local(class) => match resolved[class] {
                    Some(ty) => RegularRef::Published(ty),
                    None => RegularRef::Local(residual_index[class].expect("a class is resolved or residual")),
                },
            });
            // Putting a handle back where a symbolic node stood can let
            // clauses absorb one another, which the symbolic form had to
            // refuse. A body no substitution touched is already in normal
            // form.
            match body == class_bodies[class] {
                true => body,
                false => normalize_shape(types, body),
            }
        })
        .collect::<Vec<_>>();

    let minted = mint_residual(types, residual_bodies);
    (0..count)
        .map(|node| match handle_of(node) {
            Some(ty) => ty,
            None => minted[residual_index[classes[node]].expect("an unresolved node is residual")],
        })
        .collect()
}

/// Give the residual quotient its ids: replay an acyclic one through the
/// ordinary interner, and key a cyclic one by its rooted automaton.
fn mint_residual(types: &mut Types, bodies: Vec<DescrOf<RegularRef>>) -> Vec<Ty> {
    if bodies.iter().all(|body| !has_local_child(body)) {
        return bodies
            .into_iter()
            .map(|body| {
                types.intern(body.map_children(|reference| match reference {
                    RegularRef::Published(ty) => ty,
                    RegularRef::Local(_) => unreachable!("an acyclic quotient has no local children"),
                }))
            })
            .collect();
    }
    let keys = (0..bodies.len())
        .map(|root| rooted_key(root, &bodies))
        .collect::<Vec<_>>();

    let existing = keys
        .iter()
        .map(|key| types.interner.lookup_regular(key))
        .collect::<Vec<_>>();
    if existing.iter().any(Option::is_some) {
        assert!(
            existing.iter().all(Option::is_some),
            "a regular component was only partially present in the type interner"
        );
        return existing.into_iter().map(|ty| ty.expect("a present identity")).collect();
    }

    let descriptors = bodies
        .into_iter()
        .map(|body| {
            body.map_children(|reference| match reference {
                RegularRef::Published(ty) => ty,
                RegularRef::Local(index) => Ty((types.interner.len() + index) as u32),
            })
        })
        .collect();
    types.interner.intern_regular(keys, descriptors)
}

/// The automaton states reachable from the recursive handles this cluster
/// mentions. A handle's own children are handles again, so the set is closed:
/// once a class holds a fixed node, every class it reaches holds one too.
fn mentioned_handle_states(types: &Types, bodies: &[DescrOf<ComponentRef>]) -> Vec<Ty> {
    let mut states = BTreeSet::new();
    let mut work = Vec::new();
    for body in bodies {
        visit_children(body, |reference| {
            if let ComponentRef::Published(ty) = reference
                && types.interner.is_regular(ty)
            {
                work.push(ty);
            }
        });
    }
    while let Some(ty) = work.pop() {
        if !states.insert(ty) {
            continue;
        }
        visit_children(types.descr(&ty), |child| {
            if types.interner.is_regular(child) {
                work.push(child);
            }
        });
    }
    states.into_iter().collect()
}

/// The cluster's own bodies followed by one body per handle state, with every
/// mention of a handle rewritten to the node that now stands for it.
fn bodies_with_handle_states(
    types: &Types,
    bodies: Vec<DescrOf<ComponentRef>>,
    handles: &[Ty],
) -> Vec<DescrOf<ComponentRef>> {
    let count = bodies.len();
    let name = |reference| match reference {
        ComponentRef::Published(ty) => match handles.binary_search(&ty) {
            Ok(index) => ComponentRef::Local(NodeId(count + index)),
            Err(_) => ComponentRef::Published(ty),
        },
        local @ ComponentRef::Local(_) => local,
    };
    bodies
        .into_iter()
        .map(|body| body.map_children(name))
        .chain(handles.iter().map(|&ty| types.regular_published(ty).map_children(name)))
        .collect()
}

/// The handle each class resolves to, read off the fixed nodes that landed in
/// it. Two handles in one class would be two ids for one denotation, which is
/// the very thing this resolution exists to prevent.
fn resolved_classes(classes: &[usize], count: usize, handles: &[Ty], class_count: usize) -> Vec<Option<Ty>> {
    let mut resolved = vec![None; class_count];
    for (offset, &ty) in handles.iter().enumerate() {
        match &mut resolved[classes[count + offset]] {
            Some(existing) => assert_eq!(*existing, ty, "two recursive handles denote the same type"),
            slot @ None => *slot = Some(ty),
        }
    }
    resolved
}

/// Intern every root in an equation forest. Source-level recursion and the
/// retained descriptor graph need not have identical components: an opaque
/// declaration, for example, validates a body but retains only its nominal
/// leaf. The descriptor graph is therefore partitioned before each strongly
/// connected piece enters the regular interner.
pub(super) fn intern_bodies(types: &mut Types, bodies: Vec<DescrOf<ComponentRef>>) -> Vec<Ty> {
    let components = strongly_connected_components(&bodies);
    let mut component_of = vec![0; bodies.len()];
    for (component, members) in components.iter().enumerate() {
        for &member in members {
            component_of[member] = component;
        }
    }
    let mut resolved = vec![None; bodies.len()];
    let mut remaining = components.iter().enumerate().collect::<Vec<_>>();
    while !remaining.is_empty() {
        let ready = remaining
            .iter()
            .position(|(component, members)| {
                members.iter().all(|&member| {
                    local_children(&bodies[member])
                        .all(|child| component_of[child] == *component || resolved[child].is_some())
                })
            })
            .expect("regular descriptor components form a finite acyclic quotient");
        let (component, members) = remaining.remove(ready);
        let mut local_index = vec![None; bodies.len()];
        for (local, &global) in members.iter().enumerate() {
            local_index[global] = Some(local);
        }
        let component_bodies = members
            .iter()
            .map(|&member| {
                bodies[member].clone().map_children(|reference| match reference {
                    ComponentRef::Published(ty) => ComponentRef::Published(ty),
                    ComponentRef::Local(NodeId(child)) if component_of[child] == component => {
                        ComponentRef::local(local_index[child].expect("component member has a local id"))
                    }
                    ComponentRef::Local(NodeId(child)) => {
                        ComponentRef::Published(resolved[child].expect("outgoing descriptor component resolves first"))
                    }
                })
            })
            .collect::<Vec<_>>();
        let tys = intern(types, members.len(), |_| component_bodies);
        for (member, ty) in members.iter().copied().zip(tys) {
            resolved[member] = Some(ty);
        }
    }
    resolved
        .into_iter()
        .map(|ty| ty.expect("every descriptor root resolves"))
        .collect()
}

/// The union of two types when one of them is recursive.
///
/// Unioning two recursive types meets a new PAIR of states at every rung:
/// `{:x, B} | {:x, B'}` is one rectangle over `B | B'`, whose own rungs are
/// unions again, and for two distinct cycles that unfolding never repeats a
/// descriptor that has an identity yet. Rebuilding each rung on its own
/// therefore descends forever, with nothing for the interner's memo to
/// recognise.
///
/// So the union is built the way every other recursive value is: one body per
/// reachable pair of states, a pair met a second time closing onto the body
/// already open for it, and the collected bodies handed to the regular
/// interner, which ties the knot and assigns identity by rooted automaton. A
/// pair that turns out acyclic never reaches that interner -- its body names
/// no local sibling, so it is published as it is finished.
pub(super) fn union(types: &mut Types, a: Ty, b: Ty) -> Ty {
    let mut walk = UnionWalk {
        nodes: HashMap::new(),
        bodies: Vec::new(),
    };
    match union_node(types, &mut walk, a, b) {
        ComponentRef::Published(ty) => ty,
        // The root is the first node the walk opens, so it is body zero.
        ComponentRef::Local(_) => types.intern_regular_bodies(reachable_bodies(walk.bodies))[0],
    }
}

/// The pairs of one union under construction.
struct UnionWalk {
    nodes: HashMap<(Ty, Ty), UnionNode>,
    bodies: Vec<DescrOf<ComponentRef>>,
}

enum UnionNode {
    /// Still on the walk's own stack. Reaching it again is the back edge that
    /// makes the union recursive, and this is the body it closes onto.
    Open(usize),
    Settled(ComponentRef),
}

/// The reference standing for one pair's union.
fn union_node(types: &mut Types, walk: &mut UnionWalk, a: Ty, b: Ty) -> ComponentRef {
    if a == b {
        return ComponentRef::Published(a);
    }
    // A pair with no recursive state has no cycle to close, so it takes the
    // ordinary boundary and comes back with an identity.
    if !types.interner.is_regular(a) && !types.interner.is_regular(b) {
        return ComponentRef::Published(types.union(a, b));
    }
    let key = if a <= b { (a, b) } else { (b, a) };
    if let Some(ty) = types
        .binary_type_operations
        .lookup(BinaryTypeOperation::Union(key.0, key.1))
    {
        return ComponentRef::Published(ty);
    }
    match walk.nodes.get(&key) {
        Some(UnionNode::Settled(reference)) => return *reference,
        Some(UnionNode::Open(index)) => return ComponentRef::local(*index),
        None => {}
    }
    let index = walk.bodies.len();
    walk.bodies.push(DescrOf::none());
    walk.nodes.insert(key, UnionNode::Open(index));
    let body = union_body(types, walk, a, b);
    let reference = match types.intern_ground_regular_body(body.clone()) {
        Some(ground) => ComponentRef::Published(ground),
        None => ComponentRef::local(index),
    };
    walk.bodies[index] = body;
    walk.nodes.insert(key, UnionNode::Settled(reference));
    reference
}

/// One pair's body: both operands' clauses, carved to the one normal form, so
/// that the two coordinates a fused rectangle joins become the next pair.
fn union_body(types: &mut Types, walk: &mut UnionWalk, a: Ty, b: Ty) -> DescrOf<ComponentRef> {
    let body = {
        let cx = types.ctx();
        cx.descr(&a).union(cx, cx.descr(&b))
    }
    .map_children(ComponentRef::Published);
    canonical_brand_partition(body, |structure| {
        let mut ops = UnionTupleOps { types, walk };
        normalize_tuple_rect_clauses(&mut ops, &mut structure.tuples);
    })
}

/// The bodies the root reaches, renumbered from it.
///
/// Carving asks for the union of coordinates it may then discard, so the walk
/// can open a pair no surviving rectangle names. Dropping those before the
/// interner sees them is what keeps a speculative question from minting a
/// type.
fn reachable_bodies(bodies: Vec<DescrOf<ComponentRef>>) -> Vec<DescrOf<ComponentRef>> {
    let mut renumbered = vec![None; bodies.len()];
    let mut order = Vec::new();
    let mut work = vec![0];
    while let Some(node) = work.pop() {
        if renumbered[node].is_some() {
            continue;
        }
        renumbered[node] = Some(order.len());
        order.push(node);
        visit_children(&bodies[node], |reference| {
            if let ComponentRef::Local(NodeId(child)) = reference {
                work.push(child);
            }
        });
    }
    order
        .into_iter()
        .map(|node| {
            bodies[node].clone().map_children(|reference| match reference {
                ComponentRef::Published(ty) => ComponentRef::Published(ty),
                ComponentRef::Local(NodeId(child)) => {
                    ComponentRef::local(renumbered[child].expect("a reached body is renumbered"))
                }
            })
        })
        .collect()
}

struct UnionTupleOps<'a, 'w> {
    types: &'a mut Types,
    walk: &'w mut UnionWalk,
}

impl axis::TupleRectOps<ComponentRef> for UnionTupleOps<'_, '_> {
    fn same(&self, left: &ComponentRef, right: &ComponentRef) -> bool {
        left == right
    }

    fn union(&mut self, left: &ComponentRef, right: &ComponentRef) -> Option<ComponentRef> {
        match (*left, *right) {
            (ComponentRef::Published(left), ComponentRef::Published(right)) => {
                Some(union_node(self.types, self.walk, left, right))
            }
            _ => None,
        }
    }

    fn covered_by(&self, candidate: &[ComponentRef], rectangles: &[Vec<ComponentRef>]) -> bool {
        rectangles_cover(self.types, candidate, rectangles, |reference| match reference {
            ComponentRef::Published(ty) => Some(*ty),
            ComponentRef::Local(_) => None,
        })
    }
}

/// The list-family class of a type: the same type with every list clause it
/// holds, at every depth, admitting the empty list.
///
/// The class is built the way every other recursive value is: one body per
/// state the walk opens, a state met a second time closing onto the body
/// already open for it, and the collected bodies handed to the regular
/// interner, which ties the knot and assigns identity by rooted automaton.
/// Rebuilding each state on its own would descend forever through a cycle,
/// because the fold produces a type the walk has not been asked about yet, so
/// there is nothing for the interner's memo to recognise. A state that reaches
/// no cycle never gets that far -- its body names no local sibling, so it is
/// published as it is finished.
pub(super) fn list_family_class(types: &mut Types, ty: Ty) -> Ty {
    let mut walk = ClassWalk {
        nodes: HashMap::new(),
        bodies: Vec::new(),
    };
    match class_node(types, &mut walk, ty) {
        ComponentRef::Published(class) => class,
        // The root is the first node the walk opens, so it is body zero.
        ComponentRef::Local(_) => {
            let class = types.intern_regular_bodies(reachable_bodies(walk.bodies))[0];
            types.list_family_classes.insert(ty, class);
            class
        }
    }
}

/// The states of one list-family class under construction.
struct ClassWalk {
    nodes: HashMap<Ty, ClassNode>,
    bodies: Vec<DescrOf<ComponentRef>>,
}

enum ClassNode {
    /// Still on the walk's own stack. Reaching it again is the back edge that
    /// makes the class recursive, and this is the body it closes onto.
    Open(usize),
    Settled(ComponentRef),
}

/// The reference standing for one state's class.
fn class_node(types: &mut Types, walk: &mut ClassWalk, ty: Ty) -> ComponentRef {
    if let Some(&class) = types.list_family_classes.get(&ty) {
        return ComponentRef::Published(class);
    }
    match walk.nodes.get(&ty) {
        Some(ClassNode::Settled(reference)) => return *reference,
        Some(ClassNode::Open(index)) => return ComponentRef::local(*index),
        None => {}
    }
    let index = walk.bodies.len();
    walk.bodies.push(DescrOf::none());
    walk.nodes.insert(ty, ClassNode::Open(index));
    let body = class_body(types, walk, ty);
    let reference = match types.intern_ground_regular_body(body.clone()) {
        // A state that closed onto no open body has an identity of its own,
        // which makes it a derived fact about the type rather than a step of
        // this walk, so it is remembered for every later question.
        Some(ground) => {
            types.list_family_classes.insert(ty, ground);
            ComponentRef::Published(ground)
        }
        None => ComponentRef::local(index),
    };
    walk.bodies[index] = body;
    walk.nodes.insert(ty, ClassNode::Settled(reference));
    reference
}

/// One state's body: each child replaced by its own class, and each of this
/// state's positive list clauses widened to admit the empty list. A negative
/// clause is left alone -- it says what the type excludes, so widening it
/// would narrow the type, and `[] | [h | t]` minus `[h | t]` is how the exact
/// empty list is spelled.
fn class_body(types: &mut Types, walk: &mut ClassWalk, ty: Ty) -> DescrOf<ComponentRef> {
    let descr = types.descr(&ty).clone();
    let mut body = descr.map_children(|child| class_node(types, walk, child));
    for case in &mut body.cases {
        for clause in &mut case.structure.lists {
            for sig in &mut clause.pos {
                sig.allow_empty();
            }
        }
    }
    body
}

fn strongly_connected_components(bodies: &[DescrOf<ComponentRef>]) -> Vec<Vec<usize>> {
    let mut components = super::super::scc::strongly_connected_components(0..bodies.len(), |&node| {
        local_children(&bodies[node])
            .inspect(|&child| {
                assert!(
                    child < bodies.len(),
                    "component body refers to a node outside its component forest"
                );
            })
            .collect::<Vec<_>>()
    });
    // Member order within a component is otherwise just DFS-completion
    // order; sorting it keeps the local index every downstream `rooted_key`
    // and interner lookup assigns a member deterministic across runs.
    for component in &mut components {
        component.sort_unstable();
    }
    components
}

fn local_children(body: &DescrOf<ComponentRef>) -> impl Iterator<Item = usize> + '_ {
    let mut children = Vec::new();
    visit_children(body, |reference| {
        if let ComponentRef::Local(NodeId(child)) = reference {
            children.push(child);
        }
    });
    children.into_iter()
}

fn assert_strongly_connected(bodies: &[DescrOf<ComponentRef>]) {
    for root in 0..bodies.len() {
        let mut seen = vec![false; bodies.len()];
        let mut work = vec![root];
        while let Some(node) = work.pop() {
            if std::mem::replace(&mut seen[node], true) {
                continue;
            }
            visit_children(&bodies[node], |reference| match reference {
                ComponentRef::Published(_) => {}
                ComponentRef::Local(NodeId(child)) => {
                    assert!(
                        child < bodies.len(),
                        "component body refers to a node outside its component"
                    );
                    work.push(child);
                }
            });
        }
        assert!(
            seen.into_iter().all(|reachable| reachable),
            "regular-component nodes must form one strongly connected component"
        );
    }
}

fn refine_partition(types: &mut Types, bodies: &[DescrOf<ComponentRef>]) -> Vec<usize> {
    let mut classes = classify(
        bodies
            .iter()
            .cloned()
            .map(|body| {
                normalize_shape(
                    types,
                    body.map_children(|reference| match reference {
                        ComponentRef::Published(ty) => RegularRef::Published(ty),
                        ComponentRef::Local(_) => RegularRef::Local(0),
                    }),
                )
            })
            .collect(),
    );
    loop {
        let next = classify(
            bodies
                .iter()
                .cloned()
                .map(|body| {
                    normalize_shape(
                        types,
                        body.map_children(|reference| match reference {
                            ComponentRef::Published(ty) => RegularRef::Published(ty),
                            ComponentRef::Local(NodeId(node)) => RegularRef::Local(classes[node]),
                        }),
                    )
                })
                .collect(),
        );
        if same_partition(&next, &classes) {
            return classes;
        }
        classes = next;
    }
}

fn same_partition(left: &[usize], right: &[usize]) -> bool {
    left.iter().enumerate().all(|(index, class)| {
        left.iter()
            .enumerate()
            .all(|(other, other_class)| (*class == *other_class) == (right[index] == right[other]))
    })
}

fn classify(labels: Vec<DescrOf<RegularRef>>) -> Vec<usize> {
    let mut distinct = labels.clone();
    distinct.sort();
    distinct.dedup();
    labels
        .iter()
        .map(|label| distinct.binary_search(label).expect("partition label disappeared"))
        .collect()
}

fn quotient_bodies(
    types: &mut Types,
    bodies: &[DescrOf<ComponentRef>],
    classes: &[usize],
    class_count: usize,
) -> Vec<DescrOf<RegularRef>> {
    let mut quotient = vec![None; class_count];
    for (node, body) in bodies.iter().cloned().enumerate() {
        let class = classes[node];
        let body = normalize_shape(
            types,
            body.map_children(|reference| match reference {
                ComponentRef::Published(ty) => RegularRef::Published(ty),
                ComponentRef::Local(NodeId(child)) => RegularRef::Local(classes[child]),
            }),
        );
        match &mut quotient[class] {
            Some(existing) => assert!(existing == &body, "partition class has diverged"),
            slot @ None => *slot = Some(body),
        }
    }
    quotient
        .into_iter()
        .map(|body| body.expect("partition class has no representative"))
        .collect()
}

fn rooted_key(root: usize, bodies: &[DescrOf<RegularRef>]) -> RegularKey {
    let mut ids = vec![None; bodies.len()];
    let mut queue = VecDeque::new();
    ids[root] = Some(0);
    queue.push_back(root);
    let mut next_id = 1;
    let mut nodes = Vec::with_capacity(bodies.len());

    while let Some(node) = queue.pop_front() {
        let body = bodies[node].clone().map_children(|reference| match reference {
            RegularRef::Published(ty) => RegularRef::Published(ty),
            RegularRef::Local(child) => {
                let id = match ids[child] {
                    Some(id) => id,
                    None => {
                        let id = next_id;
                        next_id += 1;
                        ids[child] = Some(id);
                        queue.push_back(child);
                        id
                    }
                };
                RegularRef::Local(id)
            }
        });
        nodes.push(body);
    }
    assert_eq!(
        nodes.len(),
        bodies.len(),
        "component root did not reach every quotient node"
    );
    RegularKey { nodes }
}

fn normalize_shape(types: &mut Types, body: DescrOf<RegularRef>) -> DescrOf<RegularRef> {
    canonical_brand_partition(body, |structure| normalize_structure(types, structure))
}

fn normalize_structure(types: &mut Types, body: &mut StructureOf<RegularRef>) {
    let mut tuple_ops = RegularTupleOps { types };
    body.tuples = std::mem::take(&mut body.tuples)
        .into_iter()
        .map(|clause| normalize_tuple_coordinate_difference_with(&mut tuple_ops, clause))
        .collect();
    normalize_tuple_rect_clauses(&mut tuple_ops, &mut body.tuples);
    normalize_axis(&mut body.tuples);
    absorb_regular_tuple_clauses(types, &mut body.tuples);
    axis::merge_empty_list_clause(&mut body.lists);
    normalize_axis(&mut body.lists);
    let mut callable_ops = RegularCallableSurfaceOps { types };
    normalize_literal_callable_surfaces_with(&mut callable_ops, body);
    normalize_axis(&mut body.resources);
    normalize_axis(&mut body.funcs);
    normalize_axis(&mut body.maps);
}

/// The tuple axis of a body whose coordinates may still be local, carved to
/// the one normal form. A clause that is a plain rectangle goes through the
/// shared carving; anything else keeps the form it arrived in.
fn normalize_tuple_rect_clauses<R: Clone>(
    ops: &mut impl axis::TupleRectOps<R>,
    clauses: &mut Vec<Conj<TupleSigOf<R>>>,
) {
    let mut complex = Vec::with_capacity(clauses.len());
    let mut rects = Vec::with_capacity(clauses.len());
    for clause in std::mem::take(clauses) {
        match (clause.pos.as_slice(), clause.neg.as_slice()) {
            ([sig], []) => rects.push(sig.elems.clone()),
            _ => complex.push(clause),
        }
    }
    *clauses = complex;
    clauses.extend(
        axis::normalize_tuple_rects_with(ops, rects)
            .into_iter()
            .map(|elems| Conj::pos_of(TupleSigOf { elems })),
    );
}

fn absorb_regular_tuple_clauses(types: &Types, clauses: &mut Vec<Conj<super::sigs::TupleSigOf<RegularRef>>>) {
    axis::drop_directly_covered_clauses(clauses, |wider, narrower| {
        axis::tuple_clause_covers(wider, narrower, |narrower, wider| {
            regular_ref_is_subtype(types, narrower, wider)
        })
    });
}

fn regular_ref_is_subtype(types: &Types, narrower: &RegularRef, wider: &RegularRef) -> bool {
    match (*narrower, *wider) {
        (_, RegularRef::Published(wider)) if types.descr(&wider).is_full(types.ctx()) => true,
        (RegularRef::Published(narrower), RegularRef::Published(wider)) => types.is_subtype(&narrower, &wider),
        _ => narrower == wider,
    }
}

/// Whether the union of `rectangles` already contains `candidate`.
///
/// A coordinate can only feed the emptiness check once every row agrees on
/// what it names. A local (not-yet-published) coordinate is sound to compare
/// only when the candidate names that SAME node at that position in every row
/// -- the node then cancels out of the comparison symbolically, whatever it
/// turns out to mean once published. Any row that disagrees -- a different
/// local node, or a published type sitting where the candidate holds a local
/// one, or a local node sitting where the candidate holds a published type --
/// cannot be approximated (there is no sound stand-in for "the type this
/// cyclic reference will eventually have"), so covering can't be claimed at
/// all.
fn rectangles_cover<R: PartialEq>(
    types: &Types,
    candidate: &[R],
    rectangles: &[Vec<R>],
    published: impl Fn(&R) -> Option<Ty>,
) -> bool {
    let coordinates_resolved = candidate.iter().enumerate().all(|(coordinate, coordinate_ref)| {
        rectangles.iter().all(|rectangle| match published(coordinate_ref) {
            Some(_) => published(&rectangle[coordinate]).is_some(),
            None => rectangle[coordinate] == *coordinate_ref,
        })
    });
    if !coordinates_resolved {
        return false;
    }
    let describe = |reference: &R| match published(reference) {
        Some(ty) => Operand::Ty(ty),
        None => Operand::built(DescrOf::any()),
    };
    let candidate = candidate.iter().map(&describe).collect::<Vec<_>>();
    let rectangles = rectangles
        .iter()
        .map(|rectangle| rectangle.iter().map(&describe).collect())
        .collect::<Vec<_>>();
    super::emptiness::phi_tuple(
        types.ctx(),
        &candidate,
        &rectangles,
        &mut super::emptiness::Memo::default(),
    )
}

struct RegularTupleOps<'a> {
    types: &'a mut Types,
}

struct RegularCallableSurfaceOps<'a> {
    types: &'a mut Types,
}

impl CallableSurfaceOps<RegularRef> for RegularCallableSurfaceOps<'_> {
    fn named_arg(&mut self, fn_id: FnId, position: usize) -> RegularRef {
        RegularRef::Published(
            self.types
                .type_var(super::closure_surface_var::closure_var_id(fn_id, position)),
        )
    }

    fn named_ret(&mut self, fn_id: FnId) -> RegularRef {
        RegularRef::Published(
            self.types
                .type_var(super::closure_surface_var::closure_ret_var_id(fn_id)),
        )
    }
}

impl TupleCoordinateOps<RegularRef> for RegularTupleOps<'_> {
    fn is_subtype(&self, positive: &RegularRef, negative: &RegularRef) -> bool {
        regular_ref_is_subtype(self.types, positive, negative)
    }

    fn has_vars(&self, reference: &RegularRef) -> bool {
        match reference {
            RegularRef::Published(ty) => self.types.has_vars(ty),
            RegularRef::Local(_) => false,
        }
    }

    fn difference(&mut self, positive: RegularRef, negative: RegularRef) -> Option<RegularRef> {
        match (positive, negative) {
            (RegularRef::Published(positive), RegularRef::Published(negative)) => {
                Some(RegularRef::Published(self.types.difference(positive, negative)))
            }
            _ => None,
        }
    }
}

impl axis::TupleRectOps<RegularRef> for RegularTupleOps<'_> {
    fn same(&self, left: &RegularRef, right: &RegularRef) -> bool {
        left == right
    }

    fn union(&mut self, left: &RegularRef, right: &RegularRef) -> Option<RegularRef> {
        match (*left, *right) {
            (RegularRef::Published(left), RegularRef::Published(right)) => {
                Some(RegularRef::Published(self.types.union(left, right)))
            }
            _ => None,
        }
    }

    fn covered_by(&self, candidate: &[RegularRef], rectangles: &[Vec<RegularRef>]) -> bool {
        rectangles_cover(self.types, candidate, rectangles, |reference| match reference {
            RegularRef::Published(ty) => Some(*ty),
            RegularRef::Local(_) => None,
        })
    }
}

fn has_local_child(body: &DescrOf<RegularRef>) -> bool {
    let mut has_local = false;
    visit_children(body, |reference| has_local |= matches!(reference, RegularRef::Local(_)));
    has_local
}

fn visit_children<R: Copy>(body: &DescrOf<R>, mut visit: impl FnMut(R)) {
    for case in &body.cases {
        visit_structure_children(&case.structure, &mut visit);
    }
}

fn visit_structure_children<R: Copy>(body: &StructureOf<R>, visit: &mut impl FnMut(R)) {
    for clause in &body.tuples {
        for sig in clause.pos.iter().chain(&clause.neg) {
            sig.elems.iter().copied().for_each(&mut *visit);
        }
    }
    for clause in &body.lists {
        for sig in clause.pos.iter().chain(&clause.neg) {
            sig.elem.into_iter().for_each(&mut *visit);
        }
    }
    for clause in &body.resources {
        for sig in clause.pos.iter().chain(&clause.neg) {
            visit(sig.payload);
        }
    }
    for clause in &body.funcs {
        for sig in clause.pos.iter().chain(&clause.neg) {
            sig.args.iter().copied().for_each(&mut *visit);
            visit(sig.ret);
            if let Some(lit) = &sig.lit {
                lit.captures.iter().copied().for_each(&mut *visit);
            }
        }
    }
    for clause in &body.maps {
        for sig in clause.pos.iter().chain(&clause.neg) {
            sig.fields.values().copied().for_each(&mut *visit);
        }
    }
}

fn normalize_axis<T: Ord>(clauses: &mut Vec<Conj<T>>) {
    for clause in clauses.iter_mut() {
        clause.pos.sort();
        clause.pos.dedup();
        clause.neg.sort();
        clause.neg.dedup();
    }
    clauses.sort();
    clauses.dedup();
}

#[cfg(test)]
#[path = "regular_test.rs"]
mod regular_test;
