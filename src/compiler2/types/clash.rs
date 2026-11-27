//! Clash folding: a type that repeats itself folds at the point it grew.
//!
//! Van Hentenryck, Cortesi and Le Charlier (PLDI'94): compare a slot's previous
//! iterate with `old ∪ new` node by node, in correspondence. A slot whose new
//! value holds a constructor an ancestor's previous iterate already holds, and
//! whose whole value (old and new) lies inside that ancestor's joined members,
//! has repeated the ancestor: it becomes a back edge to it, which takes the
//! slot's values in. A slot value that does not lie wholly inside the ancestor
//! is ordinary growth, and so is a slot that gains only the empty list. A node whose values were already the ancestor's is a
//! cycle; otherwise it is a replacement, and the ancestor grows by the node.
//! The result is a recursive type.
//!
//! Detection is a read-only walk over interned descriptors. It builds a `Plan`
//! (paths to fold) and interns nothing; only a non-empty plan interns, and then
//! only the nodes on the folded paths. The common case, no clash, leaves the
//! interner untouched.
//!
//! A recursive type met on the walk is already its own fixpoint, so the walk
//! enters only the other members of a node. Growth is judged on those members
//! too, and a recursive member does not absorb a neighbour: tuple
//! slots gather the members of every rectangle, so a finite tree lying within
//! a recursive tree from another rectangle has still grown in its own.

use std::rc::Rc;

use super::MapKey;
use super::descr::Descr;
use super::{Ty, TypeVarId, Types, is_struct_module_key};
use crate::fast_hash::{HashMap, HashSet};

/// Whether the folded node's values lie inside the ancestor's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClashKind {
    /// The node's values are among the ancestor's: the type came back to it.
    Cycle,
    /// The node's values reach beyond the ancestor's, and the ancestor takes them in.
    Replace,
}

impl ClashKind {
    pub(crate) fn label(self) -> &'static str {
        match self {
            ClashKind::Cycle => "cycle",
            ClashKind::Replace => "replace",
        }
    }
}

/// One fold that fired: the slot path from the root, and how far up the
/// ancestor the slot returns to sits.
#[derive(Clone, Debug)]
pub(crate) struct ClashFold {
    pub path: Vec<u16>,
    pub kind: ClashKind,
    pub ancestor_depth: usize,
}

impl ClashFold {
    /// The slot path from the folded type's root, `.`-separated.
    pub(crate) fn path_label(&self) -> String {
        let slots: Vec<String> = self.path.iter().map(u16::to_string).collect();
        slots.join(".")
    }
}

/// The principal functor of one constructor clause: its kind, plus a tuple's
/// arity and at most one atom tag (the atom its first slot holds), plus a map's
/// key set. An untagged tuple head stands for every tuple of its arity.
#[derive(Clone, PartialEq)]
enum Head {
    Tuple(usize, Option<String>),
    List,
    Resource,
    Map(Vec<MapKey>),
}

/// A node's principal-functor view: per head, the clauses (rows) with that head,
/// each holding the child of every slot.
struct Pf {
    heads: Vec<(Head, Vec<Vec<Option<Ty>>>)>,
}

impl Pf {
    fn of(types: &Types, set: &[Ty]) -> Pf {
        let mut heads: Vec<(Head, Vec<Vec<Option<Ty>>>)> = Vec::new();
        for ty in set {
            let d = types.descr(ty);
            for conj in &d.tuples {
                for sig in &conj.pos {
                    for head in tuple_heads(types, &sig.elems) {
                        add(&mut heads, head, sig.elems.iter().map(|e| Some(*e)).collect());
                    }
                }
            }
            for conj in &d.lists {
                for sig in &conj.pos {
                    if let Some(cons) = sig.cons {
                        add(&mut heads, Head::List, vec![Some(cons.elem), Some(cons.last)]);
                    }
                }
            }
            for conj in &d.resources {
                for sig in &conj.pos {
                    add(&mut heads, Head::Resource, vec![Some(sig.payload)]);
                }
            }
            for conj in &d.maps {
                for sig in &conj.pos {
                    let head = Head::Map(sig.fields.keys().cloned().collect());
                    let kids = sig
                        .fields
                        .iter()
                        .map(|(k, field)| (!is_struct_module_key(k)).then_some(field.ty))
                        .chain(sig.domains.tys().map(Some))
                        .collect();
                    add(&mut heads, head, kids);
                }
            }
        }
        Pf { heads }
    }

    fn rows(&self, head: &Head) -> Option<&Vec<Vec<Option<Ty>>>> {
        self.heads.iter().find(|(h, _)| h == head).map(|(_, s)| s)
    }
}

fn add(heads: &mut Vec<(Head, Vec<Vec<Option<Ty>>>)>, head: Head, kids: Vec<Option<Ty>>) {
    if let Some((_, rows)) = heads.iter_mut().find(|(h, _)| *h == head) {
        rows.push(kids);
    } else {
        heads.push((head, vec![kids]));
    }
}

/// A tuple clause's heads: one per atom its first slot can be, or the single
/// untagged head when the first slot is not a finite set of atoms.
fn tuple_heads(types: &Types, elems: &[Ty]) -> Vec<Head> {
    let arity = elems.len();
    let tags = elems
        .first()
        .and_then(|first| atom_only(types, first))
        .and_then(|first| types.descr(&first).atom_literals());
    match tags {
        Some(tags) => tags.into_iter().map(|tag| Head::Tuple(arity, Some(tag))).collect(),
        None => vec![Head::Tuple(arity, None)],
    }
}

fn atom_only(types: &Types, ty: &Ty) -> Option<Ty> {
    let d = types.descr(ty);
    let atoms_only = d.basic == super::bits::BasicBits::NONE
        && !d.atoms.is_none()
        && !d.atoms.is_any()
        && d.tuples.is_empty()
        && d.lists.is_empty()
        && d.resources.is_empty()
        && d.funcs.is_empty()
        && d.maps.is_empty();
    atoms_only.then_some(*ty)
}

/// The constructor clauses of a descriptor, each alone: the unit growth is judged by.
fn clauses(d: &Descr) -> Vec<Descr> {
    let alone = |f: &dyn Fn(&mut Descr)| {
        let mut one = Descr { brands: d.brands.clone(), ..Descr::none() };
        f(&mut one);
        one
    };
    let mut out = Vec::new();
    out.extend(d.tuples.iter().map(|c| alone(&|o| o.tuples = vec![c.clone()])));
    out.extend(d.lists.iter().map(|c| alone(&|o| o.lists = vec![c.clone()])));
    out.extend(d.resources.iter().map(|c| alone(&|o| o.resources = vec![c.clone()])));
    out.extend(d.maps.iter().map(|c| alone(&|o| o.maps = vec![c.clone()])));
    out
}

/// What to do at one slot: fold it, or look further down.
#[derive(Clone)]
enum Cut {
    Fold(ClashKind, usize, Rc<[Ty]>),
    /// The slot holds a flat closed member that its own equation has outgrown:
    /// the slot becomes an equation of its own, taking the member's body in.
    Reopen(Rc<[Ty]>),
    Below(Rc<Plan>),
}

/// Paths to fold, keyed by (head, slot). Empty means no clash.
#[derive(Default)]
struct Plan {
    cuts: Vec<((Head, usize), Cut)>,
}

/// An ancestor frame: the node's joined members and principal functors.
struct Frame {
    members: Vec<Ty>,
    olds: Vec<Ty>,
}

struct Walk<'a> {
    types: &'a Types,
    frames: Vec<Frame>,
    seen: HashMap<(Vec<Ty>, Vec<Ty>, usize), Option<Cut>>,
    path: Vec<u16>,
    folds: Vec<ClashFold>,
    empty: Ty,
}

impl Walk<'_> {
    fn descend(&mut self, olds: &[Ty], news: &[Ty], po: &Pf, pn: &Pf) -> Rc<Plan> {
        let members: Vec<Ty> = olds.iter().chain(news).copied().collect();
        self.frames.push(Frame {
            members,
            olds: olds.to_vec(),
        });
        let mut plan = Plan::default();
        for (head, new_rows) in &pn.heads {
            let Some(old_rows) = po.rows(head) else { continue };
            let arity = new_rows.iter().chain(old_rows).map(Vec::len).min().unwrap_or(0);
            for i in 0..arity {
                let (os, ns) = self.along(old_rows, new_rows, i);
                self.path.push(i as u16);
                if let Some(cut) = self.slot(&os, &ns) {
                    plan.cuts.push(((head.clone(), i), cut));
                }
                self.path.pop();
            }
        }
        self.frames.pop();
        Rc::new(plan)
    }

    /// What slot `i` held before and holds now, read along the clauses that
    /// differ only at `i`. A new clause grows an old one along slot `i` when
    /// every other slot of the new clause lies inside the old one's; a clause
    /// already inside such an old clause has not grown. A neighbouring clause
    /// that is wide at `i` cannot hide growth in a clause that is not.
    fn along(&self, old_rows: &[Vec<Option<Ty>>], new_rows: &[Vec<Option<Ty>>], i: usize) -> (Vec<Ty>, Vec<Ty>) {
        let types = self.types;
        let inside = |a: &Option<Ty>, b: &Option<Ty>| match (a, b) {
            (Some(a), Some(b)) => types.is_subtype(a, b),
            (None, None) => true,
            _ => false,
        };
        let (mut os, mut ns) = (Vec::new(), Vec::new());
        for new in new_rows {
            let Some(n) = new[i] else { continue };
            let paired: Vec<Ty> = old_rows
                .iter()
                .filter(|old| new.iter().zip(old.iter()).enumerate().all(|(j, (a, b))| j == i || inside(a, b)))
                .filter_map(|old| old[i])
                .collect();
            if paired.iter().any(|o| types.is_subtype(&n, o)) {
                continue;
            }
            os.extend(paired.into_iter().filter(|o| !os.contains(o)).collect::<Vec<_>>());
            if !ns.contains(&n) {
                ns.push(n);
            }
        }
        if os.is_empty() || ns.is_empty() {
            let column = |rows: &[Vec<Option<Ty>>]| -> Vec<Ty> { rows.iter().filter_map(|r| r[i]).collect() };
            return (column(old_rows), column(new_rows));
        }
        (os, ns)
    }

    fn slot(&mut self, os: &[Ty], ns: &[Ty]) -> Option<Cut> {
        let types = self.types;
        let live: Vec<Ty> = ns
            .iter()
            .copied()
            .filter(|n| {
                !types.is_empty(n)
                    && !os
                        .iter()
                        .any(|o| !types.is_recursive_member(o) && self.holds_but_for_empty(n, o))
            })
            .collect();
        let olds: Vec<Ty> = os.iter().copied().filter(|o| !types.is_empty(o)).collect();
        if live.is_empty() || olds.is_empty() {
            return None;
        }
        let key = (olds, live, self.frames.len());
        if let Some(cut) = self.seen.get(&key).cloned() {
            if let Some(Cut::Fold(kind, depth, _)) = &cut {
                self.folds.push(ClashFold {
                    path: self.path.clone(),
                    kind: *kind,
                    ancestor_depth: *depth,
                });
            }
            return cut;
        }
        let cut = self.judge(&key.0, &key.1);
        self.seen.insert(key, cut.clone());
        cut
    }

    /// `new` lies inside `old`, or inside `old` together with the empty list.
    fn holds_but_for_empty(&self, new: &Ty, old: &Ty) -> bool {
        let types = self.types;
        let cx = types.ctx();
        let with_empty = types.descr(old).union(cx, types.descr(&self.empty));
        types.is_subtype(new, old) || types.descr(new).is_subtype(cx, &with_empty)
    }

    /// The innermost ancestor frame whose old members hold a constructor
    /// clause of a live child, and whose joined members hold every
    /// constructor clause of the slot's old values.
    fn returned_ancestor(&self, olds: &[Ty], live: &[Ty]) -> Option<usize> {
        let types = self.types;
        let returns = |f: &Frame| {
            live.iter().any(|n| types.holds_a_clause_within(n, &f.olds))
                && olds.iter().all(|n| !types.has_clause_outside(n, &f.members))
        };
        let whole = |f: &Frame| live.iter().all(|n| !types.has_clause_outside(n, &f.members));
        self.frames
            .iter()
            .rposition(|f| returns(f) && whole(f))
            .or_else(|| self.frames.iter().rposition(returns))
    }

    fn judge(&mut self, olds: &[Ty], live: &[Ty]) -> Option<Cut> {
        let types = self.types;
        if let Some(depth) = self.returned_ancestor(olds, live) {
            let members: Vec<Ty> = olds.iter().chain(live).copied().collect();
            let kind = self.kind(&members, &self.frames[depth].members);
            self.folds.push(ClashFold {
                path: self.path.clone(),
                kind,
                ancestor_depth: depth,
            });
            return Some(Cut::Fold(kind, depth, self.frames[depth].members.as_slice().into()));
        }
        let reopened: Vec<Ty> = olds
            .iter()
            .copied()
            .filter(|o| types.is_recursive_member(o) && live.iter().any(|n| n != o && types.mentions(n, o)))
            .filter(|o| !types.has_nested_member(o) && self.no_new_head(o, live))
            .collect();
        if !reopened.is_empty() {
            self.folds.push(ClashFold {
                path: self.path.clone(),
                kind: ClashKind::Replace,
                ancestor_depth: self.frames.len(),
            });
            return Some(Cut::Reopen(reopened.as_slice().into()));
        }
        let walked = |set: &[Ty]| -> Vec<Ty> {
            set.iter()
                .copied()
                .filter(|ty| !types.is_recursive_member(ty))
                .collect()
        };
        let (po, pn) = (Pf::of(types, &walked(olds)), Pf::of(types, &walked(live)));
        let sub = self.descend(olds, live, &po, &pn);
        (!sub.cuts.is_empty()).then_some(Cut::Below(sub))
    }

    /// Every principal functor `live` holds besides `member` is one `member`'s own equation has.
    fn no_new_head(&self, member: &Ty, live: &[Ty]) -> bool {
        let types = self.types;
        let own = Pf::of(types, &[*member]);
        let others: Vec<Ty> = live.iter().copied().filter(|n| n != member).collect();
        let theirs = Pf::of(types, &others);
        theirs.heads.iter().all(|(h, _)| own.rows(h).is_some())
    }

    fn kind(&self, node: &[Ty], ancestor: &[Ty]) -> ClashKind {
        let cx = self.types.ctx();
        let union = |set: &[Ty]| {
            set.iter()
                .fold(Descr::none(), |acc, t| acc.union(cx, self.types.descr(t)))
        };
        if union(node).is_subtype(cx, &union(ancestor)) {
            ClashKind::Cycle
        } else {
            ClashKind::Replace
        }
    }
}

impl Types {
    /// Some constructor clause of `ty` lies inside one of `set`.
    fn holds_a_clause_within(&self, ty: &Ty, set: &[Ty]) -> bool {
        let cx = self.ctx();
        if self.is_recursive_member(ty) {
            return self.descr(ty).has_constructors() && set.iter().any(|m| self.is_subtype(ty, m));
        }
        clauses(self.descr(ty)).iter().any(|c| set.iter().any(|m| c.is_subtype(cx, self.descr(m))))
    }

    /// Some constructor clause of `ty` lies inside none of `set`: leaves are free.
    fn has_clause_outside(&self, ty: &Ty, set: &[Ty]) -> bool {
        let cx = self.ctx();
        if self.is_recursive_member(ty) {
            return self.descr(ty).has_constructors() && !set.iter().any(|m| self.is_subtype(ty, m));
        }
        clauses(self.descr(ty)).iter().any(|c| !set.iter().any(|m| c.is_subtype(cx, self.descr(m))))
    }

    /// `child` split into the constructor clauses that lie inside `set`, and the rest: its leaves and the clauses that do not.
    fn split_within(&mut self, child: Ty, set: &[Ty]) -> (Ty, Ty) {
        if self.is_recursive_member(&child) {
            let held = set.iter().any(|m| self.is_subtype(&child, m));
            return if held { (child, self.none()) } else { (self.none(), child) };
        }
        let d = self.descr(&child).clone();
        let cx = self.ctx();
        let (mut inside, mut rest) = (Descr { brands: d.brands.clone(), ..Descr::none() }, d.clone());
        macro_rules! split {
            ($field:ident) => {
                rest.$field = Vec::new();
                for c in &d.$field {
                    let mut one = Descr { brands: d.brands.clone(), ..Descr::none() };
                    one.$field = vec![c.clone()];
                    if set.iter().any(|m| one.is_subtype(cx, self.descr(m))) {
                        inside.$field.push(c.clone());
                    } else {
                        rest.$field.push(c.clone());
                    }
                }
            };
        }
        split!(tuples);
        split!(lists);
        split!(resources);
        split!(maps);
        (self.intern(inside), self.intern(rest))
    }

    /// Some recursive member lies inside `ty` other than `ty` itself.
    pub(super) fn has_nested_member(&self, ty: &Ty) -> bool {
        let children = self.descr(ty).children().map(|(c, _)| c).collect();
        self.reaches(children, |t| t != *ty && self.is_recursive_member(&t), |t| t != *ty)
    }

    /// `ty` reaches `member` without passing through another recursive member.
    pub(super) fn mentions(&self, ty: &Ty, member: &Ty) -> bool {
        self.reaches(
            vec![*ty],
            |t| t == *member,
            |t| t == *ty || !self.is_recursive_member(&t),
        )
    }

    /// Some type reachable from `start` satisfies `hit`, walking only through types that satisfy `enter`.
    fn reaches(&self, start: Vec<Ty>, hit: impl Fn(Ty) -> bool, enter: impl Fn(Ty) -> bool) -> bool {
        let mut seen = HashSet::default();
        let mut stack = start;
        while let Some(t) = stack.pop() {
            if hit(t) {
                return true;
            }
            if seen.insert(t) && enter(t) {
                stack.extend(self.descr(&t).children().map(|(c, _)| c));
            }
        }
        false
    }

    /// `ty` with every occurrence of `members` replaced by `var`; `open` keeps `ty`'s own top node.
    pub(super) fn replace_members(&mut self, ty: Ty, members: &[Ty], var: Ty, open: bool) -> Ty {
        if !open && members.contains(&ty) {
            return var;
        }
        if !open && self.is_recursive_member(&ty) {
            return ty;
        }
        let mut d = self.descr(&ty).clone();
        d.map_children(&mut |child, _| self.replace_members(child, members, var, false));
        self.intern(d)
    }
}

impl Types {
    /// Whether any of `tys` has a tuple, list, resource or map alternative.
    pub(crate) fn any_carries_constructors(&self, tys: &[Ty]) -> bool {
        tys.iter().any(|ty| self.descr(ty).has_constructors())
    }

    /// Take the folds noted since the last drain. Ask
    /// [`World::take_clash_folds`](crate::compiler2::world::World::take_clash_folds):
    /// the drain is the `World`'s to offer, and this is where they are kept.
    pub(crate) fn take_clash_folds(&mut self) -> Vec<ClashFold> {
        std::mem::take(&mut self.clash_folds)
    }

    /// The join `joined` grows into by taking in `contribution`, folded where
    /// it clashes with `joined`. `None` (and nothing interned) when the
    /// contribution cannot make the join climb: it is already inside it, or
    /// it holds no tuple, list, resource or map for a clash to be found in.
    pub(crate) fn clash_fold_join(&mut self, joined: Ty, contribution: Ty) -> Option<Ty> {
        if !self.descr(&contribution).has_constructors() || self.is_subtype(&contribution, &joined) {
            return None;
        }
        let grown = self.union(joined, contribution);
        self.clash_fold(joined, grown)
    }

    /// Fold `new` where it clashes with the previous iterate `old` under an
    /// ancestor that already holds its whole value. `None` (and nothing interned) when no
    /// slot clashes. Each fold that fires is noted for
    /// [`Types::take_clash_folds`].
    pub(crate) fn clash_fold(&mut self, old: Ty, new: Ty) -> Option<Ty> {
        if old == new || !self.descr(&old).has_constructors() || !self.descr(&new).has_constructors() {
            return None;
        }
        if self.is_empty(&old) || self.is_empty(&new) || self.is_subtype(&new, &old) {
            return None;
        }
        let empty = self.empty_list();
        let mut walk = Walk {
            types: self,
            frames: Vec::new(),
            seen: HashMap::default(),
            path: Vec::new(),
            folds: Vec::new(),
            empty,
        };
        let (po, pn) = (Pf::of(walk.types, &[old]), Pf::of(walk.types, &[new]));
        let plan = walk.descend(&[old], &[new], &po, &pn);
        let folds = std::mem::take(&mut walk.folds);
        if plan.cuts.is_empty() {
            return None;
        }
        let folded = self.apply_plan(new, &plan);
        if folded == new {
            return None;
        }
        self.clash_folds.extend(folds);
        Some(folded)
    }

    /// `ty` with every fold in `plan` made a back edge. Each node the plan
    /// rebuilds is an equation; a fold at a slot names the returned-to
    /// ancestor's equation there and adds the slot's node to it, so the
    /// ancestor holds every value it held and the node's too. Where the node's
    /// values were already the ancestor's (a cycle) that adds nothing.
    fn apply_plan(&mut self, ty: Ty, plan: &Plan) -> Ty {
        let mut equations = Equations::default();
        self.rebuild(ty, plan, &mut Vec::new(), &mut equations);
        let bodies: Vec<Ty> = equations
            .bodies
            .iter()
            .map(|body| body.expect("every rebuilt node has its right-hand side"))
            .collect();
        self.solve_equations(&equations.binders, &bodies)[0]
    }

    /// The binder of the equation for `ty` rebuilt by `plan`, under the
    /// equations of the rebuilt nodes above it, outermost first.
    fn rebuild(&mut self, ty: Ty, plan: &Plan, ancestors: &mut Vec<usize>, equations: &mut Equations) -> Ty {
        let me = equations.binders.len();
        let binder = self.mint_binder();
        equations.binders.push(binder);
        equations.bodies.push(None);
        equations.joined.push(self.none());
        ancestors.push(me);
        let mut d = self.descr(&ty).clone();
        let mut at = |types: &mut Types, heads: &[Head], i: usize, child: Ty| -> Ty {
            let Some(cut) = plan
                .cuts
                .iter()
                .find(|(k, _)| heads.contains(&k.0) && k.1 == i)
                .map(|(_, c)| c)
            else {
                return child;
            };
            match cut {
                Cut::Fold(_, depth, members) => {
                    let ancestor = ancestors[*depth];
                    let var = types.type_var(equations.binders[ancestor]);
                    let (inside, rest) = types.split_within(child, members);
                    let held = members.iter().fold(types.none(), |acc, m| types.union(acc, *m));
                    let rest = types.difference(rest, held);
                    if !types.descr(&child).has_constructors() || types.is_empty(&inside) {
                        return types.union(child, var);
                    }
                    equations.joined[ancestor] = types.union(equations.joined[ancestor], inside);
                    types.union(rest, var)
                }
                Cut::Reopen(members) => {
                    let me = equations.binders.len();
                    let binder = types.mint_binder();
                    equations.binders.push(binder);
                    equations.bodies.push(None);
                    equations.joined.push(types.none());
                    let var = types.type_var(binder);
                    let mut body = types.replace_members(child, members, var, false);
                    for member in members.iter() {
                        let opened = types.replace_members(*member, members, var, true);
                        body = types.union(body, opened);
                    }
                    equations.bodies[me] = Some(body);
                    var
                }
                Cut::Below(sub) => types.rebuild(child, sub, ancestors, equations),
            }
        };
        for conj in &mut d.tuples {
            for sig in &mut conj.pos {
                let heads = tuple_heads(self, &sig.elems);
                for (i, elem) in sig.elems.iter_mut().enumerate() {
                    *elem = at(self, &heads, i, *elem);
                }
            }
        }
        for conj in &mut d.lists {
            for sig in &mut conj.pos {
                if let Some(cons) = &mut sig.cons {
                    cons.elem = at(self, &[Head::List], 0, cons.elem);
                    cons.last = at(self, &[Head::List], 1, cons.last);
                }
            }
        }
        for conj in &mut d.resources {
            for sig in &mut conj.pos {
                sig.payload = at(self, &[Head::Resource], 0, sig.payload);
            }
        }
        for conj in &mut d.maps {
            for sig in &mut conj.pos {
                let head = [Head::Map(sig.fields.keys().cloned().collect())];
                let named = sig.fields.len();
                for (i, (k, field)) in sig.fields.iter_mut().enumerate() {
                    if !is_struct_module_key(k) {
                        field.ty = at(self, &head, i, field.ty);
                    }
                }
                for (i, ty) in sig.domains.tys_mut().enumerate() {
                    *ty = at(self, &head, named + i, *ty);
                }
            }
        }
        ancestors.pop();
        let rebuilt = self.intern(d);
        let body = self.union(rebuilt, equations.joined[me]);
        equations.bodies[me] = Some(body);
        self.type_var(binder)
    }
}

/// The equations a fold writes: one per rebuilt node, in the order the nodes
/// were entered, with what folds below each have joined into it.
#[derive(Default)]
struct Equations {
    binders: Vec<TypeVarId>,
    bodies: Vec<Option<Ty>>,
    joined: Vec<Ty>,
}

#[cfg(test)]
#[path = "clash_test.rs"]
mod clash_test;
