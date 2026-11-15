//! Clash folding: a type that repeats itself folds at the point it grew.
//!
//! Van Hentenryck, Cortesi and Le Charlier (PLDI'94): compare a slot's previous
//! iterate with `old ∪ new` node by node, in correspondence. A node CLASHES when
//! its set of principal functors grew; the clash folds to `any` when an
//! ancestor's principal functors already cover it (the type has repeated
//! itself, so the fold is a cycle back to that ancestor; if the ancestor does
//! not contain the node's values it is a replacement).
//!
//! Detection is a read-only walk over interned descriptors. It builds a `Plan`
//! (paths to fold) and interns nothing; only `fold` of a non-empty plan
//! interns, and then only the nodes on the folded paths. The common case, no
//! clash, leaves the interner untouched.

use std::rc::Rc;

use super::MapKey;
use super::descr::Descr;
use super::{Ty, Types, is_struct_module_key};
use crate::fast_hash::HashMap;

/// Whether the folded node's values lie inside the ancestor's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClashKind {
    /// The node's values are among the ancestor's: the type came back to it.
    Cycle,
    /// The ancestor covers the node's functors but not all of its values.
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
/// covering ancestor sits.
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

/// The principal functor of one constructor clause: kind, plus tuple arity and
/// the atom tag in first position, plus a map's key set.
#[derive(Clone, PartialEq)]
enum Head {
    Tuple(Vec<Option<Ty>>),
    List,
    Resource,
    Map(Vec<MapKey>),
}

/// A node's principal-functor view: the non-constructor part, and per head the
/// children of each slot across every clause with that head.
struct Pf {
    leaf: Descr,
    heads: Vec<(Head, Vec<Vec<Ty>>)>,
}

impl Pf {
    fn of(types: &Types, set: &[Ty]) -> Pf {
        let cx = types.ctx();
        let mut leaf = Descr::none();
        let mut heads: Vec<(Head, Vec<Vec<Ty>>)> = Vec::new();
        for ty in set {
            let d = types.descr(ty);
            let mut l = d.clone();
            l.tuples.clear();
            l.lists.clear();
            l.resources.clear();
            l.maps.clear();
            leaf = leaf.union(cx, &l);
            for conj in &d.tuples {
                for sig in &conj.pos {
                    let head = Head::Tuple(
                        sig.elems
                            .iter()
                            .enumerate()
                            .map(|(i, e)| if i == 0 { atom_only(types, e) } else { None })
                            .collect(),
                    );
                    add(&mut heads, head, sig.elems.iter().map(|e| Some(*e)).collect());
                }
            }
            for conj in &d.lists {
                for sig in &conj.pos {
                    if let Some(e) = sig.elem {
                        add(&mut heads, Head::List, vec![Some(e)]);
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
                        .map(|(k, v)| (!is_struct_module_key(k)).then_some(*v))
                        .collect();
                    add(&mut heads, head, kids);
                }
            }
        }
        Pf { leaf, heads }
    }

    fn slots(&self, head: &Head) -> Option<&Vec<Vec<Ty>>> {
        self.heads.iter().find(|(h, _)| h == head).map(|(_, s)| s)
    }

    /// `other`'s principal functors are all among ours.
    fn covers(&self, types: &Types, other: &Pf) -> bool {
        other.leaf.is_subtype(types.ctx(), &self.leaf) && other.heads.iter().all(|(h, _)| self.slots(h).is_some())
    }
}

/// The node's principal functors grew past the previous iterate's.
fn grew(types: &Types, old: &Pf, new: &Pf) -> bool {
    !new.leaf.is_subtype(types.ctx(), &old.leaf) || new.heads.iter().any(|(h, _)| old.slots(h).is_none())
}

fn add(heads: &mut Vec<(Head, Vec<Vec<Ty>>)>, head: Head, kids: Vec<Option<Ty>>) {
    if let Some((_, slots)) = heads.iter_mut().find(|(h, _)| *h == head) {
        for (slot, kid) in slots.iter_mut().zip(kids) {
            slot.extend(kid);
        }
    } else {
        heads.push((head, kids.into_iter().map(|k| k.into_iter().collect()).collect()));
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

/// What to do at one slot: fold it, or look further down.
#[derive(Clone)]
enum Cut {
    Fold(ClashKind, usize),
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
    pf: Pf,
}

struct Walk<'a> {
    types: &'a Types,
    frames: Vec<Frame>,
    seen: HashMap<(Vec<Ty>, Vec<Ty>, usize), Option<Cut>>,
    path: Vec<u16>,
    folds: Vec<ClashFold>,
}

impl Walk<'_> {
    fn descend(&mut self, olds: &[Ty], news: &[Ty], po: &Pf, pn: &Pf) -> Rc<Plan> {
        let members: Vec<Ty> = olds.iter().chain(news).copied().collect();
        let joined = Pf::of(self.types, &members);
        self.frames.push(Frame { members, pf: joined });
        let mut plan = Plan::default();
        for (head, new_slots) in &pn.heads {
            let Some(old_slots) = po.slots(head) else { continue };
            for (i, (os, ns)) in old_slots.iter().zip(new_slots).enumerate() {
                self.path.push(i as u16);
                if let Some(cut) = self.slot(os, ns) {
                    plan.cuts.push(((head.clone(), i), cut));
                }
                self.path.pop();
            }
        }
        self.frames.pop();
        Rc::new(plan)
    }

    fn slot(&mut self, os: &[Ty], ns: &[Ty]) -> Option<Cut> {
        let types = self.types;
        let live: Vec<Ty> = ns
            .iter()
            .copied()
            .filter(|n| !types.is_empty(n) && !os.iter().any(|o| types.is_subtype(n, o)))
            .collect();
        let olds: Vec<Ty> = os.iter().copied().filter(|o| !types.is_empty(o)).collect();
        if live.is_empty() || olds.is_empty() {
            return None;
        }
        let key = (olds, live, self.frames.len());
        if let Some(cut) = self.seen.get(&key).cloned() {
            if let Some(Cut::Fold(kind, depth)) = &cut {
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

    fn judge(&mut self, olds: &[Ty], live: &[Ty]) -> Option<Cut> {
        let types = self.types;
        let (po, pn) = (Pf::of(types, olds), Pf::of(types, live));
        if !grew(types, &po, &pn) {
            let sub = self.descend(olds, live, &po, &pn);
            return (!sub.cuts.is_empty()).then_some(Cut::Below(sub));
        }
        let members: Vec<Ty> = olds.iter().chain(live).copied().collect();
        let here = Pf::of(types, &members);
        let depth = self.frames.iter().rposition(|f| f.pf.covers(types, &here))?;
        let kind = self.kind(&members, &self.frames[depth].members);
        self.folds.push(ClashFold {
            path: self.path.clone(),
            kind,
            ancestor_depth: depth,
        });
        Some(Cut::Fold(kind, depth))
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
    /// Take the folds noted since the last drain. Ask
    /// [`World::take_clash_folds`](crate::compiler2::world::World::take_clash_folds):
    /// the drain is the `World`'s to offer, and this is where they are kept.
    pub(crate) fn take_clash_folds(&mut self) -> Vec<ClashFold> {
        std::mem::take(&mut self.clash_folds)
    }

    /// Fold `new` where it clashes with the previous iterate `old` under an
    /// ancestor that already covers it. `None` (and nothing interned) when no
    /// slot clashes. Each fold that fires is noted for
    /// [`Types::take_clash_folds`].
    pub(crate) fn clash_fold(&mut self, old: Ty, new: Ty) -> Option<Ty> {
        if old == new || !self.descr(&old).has_constructors() || !self.descr(&new).has_constructors() {
            return None;
        }
        if self.is_empty(&old) || self.is_empty(&new) || self.is_subtype(&new, &old) {
            return None;
        }
        let mut walk = Walk {
            types: self,
            frames: Vec::new(),
            seen: HashMap::default(),
            path: Vec::new(),
            folds: Vec::new(),
        };
        let (po, pn) = (Pf::of(walk.types, &[old]), Pf::of(walk.types, &[new]));
        if grew(walk.types, &po, &pn) {
            return None;
        }
        let plan = walk.descend(&[old], &[new], &po, &pn);
        let folds = std::mem::take(&mut walk.folds);
        if plan.cuts.is_empty() {
            return None;
        }
        let folded = self.apply_plan(new, &plan);
        self.clash_folds.extend(folds);
        Some(folded)
    }

    fn apply_plan(&mut self, ty: Ty, plan: &Plan) -> Ty {
        let any = self.any();
        let mut d = self.descr(&ty).clone();
        let cut_at = |head: &Head, i: usize| plan.cuts.iter().find(|(k, _)| k.0 == *head && k.1 == i).map(|(_, c)| c);
        let apply = |types: &mut Types, head: &Head, i: usize, child: Ty| -> Ty {
            match cut_at(head, i) {
                Some(Cut::Fold(..)) => any,
                Some(Cut::Below(sub)) => types.apply_plan(child, sub),
                None => child,
            }
        };
        for conj in &mut d.tuples {
            for sig in &mut conj.pos {
                let head = Head::Tuple(
                    sig.elems
                        .iter()
                        .enumerate()
                        .map(|(i, e)| if i == 0 { atom_only(self, e) } else { None })
                        .collect(),
                );
                let elems = sig.elems.clone();
                sig.elems = elems
                    .iter()
                    .enumerate()
                    .map(|(i, e)| apply(self, &head, i, *e))
                    .collect();
            }
        }
        for conj in &mut d.lists {
            for sig in &mut conj.pos {
                sig.elem = sig.elem.map(|e| apply(self, &Head::List, 0, e));
            }
        }
        for conj in &mut d.resources {
            for sig in &mut conj.pos {
                sig.payload = apply(self, &Head::Resource, 0, sig.payload);
            }
        }
        for conj in &mut d.maps {
            for sig in &mut conj.pos {
                let head = Head::Map(sig.fields.keys().cloned().collect());
                let fields = sig.fields.clone();
                for (i, (k, v)) in fields.iter().enumerate() {
                    if !is_struct_module_key(k) {
                        sig.fields.insert(k.clone(), apply(self, &head, i, *v));
                    }
                }
            }
        }
        self.intern(d)
    }
}

#[cfg(test)]
#[path = "clash_test.rs"]
mod clash_test;
