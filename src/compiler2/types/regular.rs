use std::collections::VecDeque;

use super::axis;
use super::conj::Conj;
use super::descr::DescrOf;
use super::{
    CallableSurfaceOps, TupleCoordinateOps, Ty, Types, normalize_literal_callable_surfaces_with,
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

    let classes = refine_partition(types, &bodies);
    let class_count = classes.iter().copied().max().map_or(0, |class| class + 1);
    let class_bodies = quotient_bodies(types, &bodies, &classes, class_count);
    if class_bodies.iter().all(|body| !has_local_child(body)) {
        let interned = class_bodies
            .iter()
            .cloned()
            .map(|body| {
                types.intern(body.map_children(|reference| match reference {
                    RegularRef::Published(ty) => ty,
                    RegularRef::Local(_) => unreachable!("an acyclic quotient has no local children"),
                }))
            })
            .collect::<Vec<_>>();
        return classes.into_iter().map(|class| interned[class]).collect();
    }
    let keys = (0..class_count)
        .map(|class| rooted_key(class, &class_bodies))
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
        return classes.into_iter().map(|class| existing[class].unwrap()).collect();
    }

    let descriptors = class_bodies
        .into_iter()
        .map(|body| {
            body.map_children(|reference| match reference {
                RegularRef::Published(ty) => ty,
                RegularRef::Local(class) => Ty((types.interner.len() + class) as u32),
            })
        })
        .collect();
    let interned = types.interner.intern_regular(keys, descriptors);
    classes.into_iter().map(|class| interned[class]).collect()
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

fn strongly_connected_components(bodies: &[DescrOf<ComponentRef>]) -> Vec<Vec<usize>> {
    fn visit(
        node: usize,
        bodies: &[DescrOf<ComponentRef>],
        next_index: &mut usize,
        indices: &mut [Option<usize>],
        lowlinks: &mut [usize],
        stack: &mut Vec<usize>,
        active: &mut [bool],
        components: &mut Vec<Vec<usize>>,
    ) {
        indices[node] = Some(*next_index);
        lowlinks[node] = *next_index;
        *next_index += 1;
        stack.push(node);
        active[node] = true;
        for child in local_children(&bodies[node]) {
            assert!(
                child < bodies.len(),
                "component body refers to a node outside its component forest"
            );
            if indices[child].is_none() {
                visit(child, bodies, next_index, indices, lowlinks, stack, active, components);
                lowlinks[node] = lowlinks[node].min(lowlinks[child]);
            } else if active[child] {
                lowlinks[node] = lowlinks[node].min(indices[child].expect("active node has an index"));
            }
        }
        if lowlinks[node] == indices[node].expect("visited node has an index") {
            let mut component = Vec::new();
            loop {
                let member = stack.pop().expect("component root is on the stack");
                active[member] = false;
                component.push(member);
                if member == node {
                    break;
                }
            }
            component.sort_unstable();
            components.push(component);
        }
    }

    let mut next_index = 0;
    let mut indices = vec![None; bodies.len()];
    let mut lowlinks = vec![0; bodies.len()];
    let mut stack = Vec::new();
    let mut active = vec![false; bodies.len()];
    let mut components = Vec::new();
    for node in 0..bodies.len() {
        if indices[node].is_none() {
            visit(
                node,
                bodies,
                &mut next_index,
                &mut indices,
                &mut lowlinks,
                &mut stack,
                &mut active,
                &mut components,
            );
        }
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

fn normalize_shape(types: &mut Types, mut body: DescrOf<RegularRef>) -> DescrOf<RegularRef> {
    let mut tuple_ops = RegularTupleOps { types };
    body.tuples = std::mem::take(&mut body.tuples)
        .into_iter()
        .map(|clause| normalize_tuple_coordinate_difference_with(&mut tuple_ops, clause))
        .collect();
    normalize_regular_tuple_axis(&mut tuple_ops, &mut body.tuples);
    normalize_axis(&mut body.tuples);
    absorb_regular_tuple_clauses(types, &mut body.tuples);
    axis::merge_empty_list_clause(&mut body.lists);
    normalize_axis(&mut body.lists);
    let mut callable_ops = RegularCallableSurfaceOps { types };
    normalize_literal_callable_surfaces_with(&mut callable_ops, &mut body);
    normalize_axis(&mut body.resources);
    normalize_axis(&mut body.funcs);
    normalize_axis(&mut body.maps);
    body
}

fn normalize_regular_tuple_axis(
    ops: &mut RegularTupleOps<'_>,
    clauses: &mut Vec<Conj<super::sigs::TupleSigOf<RegularRef>>>,
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
            .map(|elems| Conj::pos_of(super::sigs::TupleSigOf { elems })),
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

    fn any(&mut self) -> RegularRef {
        RegularRef::Published(self.types.any())
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
        let fixed_local_coordinates = candidate.iter().enumerate().all(|(coordinate, candidate)| {
            matches!(candidate, RegularRef::Local(_))
                .then(|| rectangles.iter().all(|rectangle| rectangle[coordinate] == *candidate))
                .unwrap_or(true)
        });
        if !fixed_local_coordinates {
            return false;
        }
        let describe = |reference| match reference {
            RegularRef::Published(ty) => self.types.descr(&ty).clone(),
            RegularRef::Local(_) => DescrOf::any(),
        };
        let candidate = candidate.iter().copied().map(describe).collect::<Vec<_>>();
        let rectangles = rectangles
            .iter()
            .map(|rectangle| rectangle.iter().copied().map(describe).collect())
            .collect::<Vec<_>>();
        super::emptiness::phi_tuple(
            self.types.ctx(),
            &candidate,
            &rectangles,
            &mut super::emptiness::Memo::default(),
        )
    }
}

fn has_local_child(body: &DescrOf<RegularRef>) -> bool {
    let mut has_local = false;
    visit_children(body, |reference| has_local |= matches!(reference, RegularRef::Local(_)));
    has_local
}

fn visit_children<R: Copy>(body: &DescrOf<R>, mut visit: impl FnMut(R)) {
    for clause in &body.tuples {
        for sig in clause.pos.iter().chain(&clause.neg) {
            sig.elems.iter().copied().for_each(&mut visit);
        }
    }
    for clause in &body.lists {
        for sig in clause.pos.iter().chain(&clause.neg) {
            sig.elem.into_iter().for_each(&mut visit);
        }
    }
    for clause in &body.resources {
        for sig in clause.pos.iter().chain(&clause.neg) {
            visit(sig.payload);
        }
    }
    for clause in &body.funcs {
        for sig in clause.pos.iter().chain(&clause.neg) {
            sig.args.iter().copied().for_each(&mut visit);
            visit(sig.ret);
            if let Some(lit) = &sig.lit {
                lit.captures.iter().copied().for_each(&mut visit);
            }
        }
    }
    for clause in &body.maps {
        for sig in clause.pos.iter().chain(&clause.neg) {
            sig.fields.values().copied().for_each(&mut visit);
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
