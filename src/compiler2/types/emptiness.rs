//! Per-axis emptiness algorithms for the interned descriptor kernel.

use crate::fz_ir::FnId;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

use super::conj::Conj;
use super::descr::Descr;
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapDomain, MapField, MapSig, ResourceSig, TupleSig};
use super::{MapKey, Ty, TyCtx};

pub(crate) fn tuple_clause_empty(cx: TyCtx<'_>, c: &Conj<TupleSig>) -> bool {
    if c.pos.is_empty() {
        return false;
    }
    let arity = c.pos[0].elems.len();
    if c.pos.iter().any(|p| p.elems.len() != arity) {
        return true;
    }
    let met: Vec<Descr> = match &c.pos[1..] {
        [] => Vec::new(),
        rest => rest.iter().fold(
            c.pos[0].elems.iter().map(|ty| cx.descr(ty).clone()).collect(),
            |met: Vec<Descr>, p| {
                met.iter()
                    .zip(&p.elems)
                    .map(|(m, e)| m.intersect(cx.descr(e)))
                    .collect()
            },
        ),
    };
    // One positive signature leaves its coordinates as the interned types they
    // are, and an interned type other than none is inhabited: its clauses were
    // all kept because none was empty. So a coordinate is empty exactly when it
    // is none, with no walk below it — unless it is a node of a recursive
    // equation still being solved (`TyCtx::coordinate_empty`). A meet of several positives is a fresh
    // descriptor, which only a walk can judge.
    let interned_coordinates = met.is_empty();
    let t: Vec<&Descr> = if interned_coordinates {
        c.pos[0].elems.iter().map(|ty| cx.descr(ty)).collect()
    } else {
        met.iter().collect()
    };
    let negs: Vec<Vec<&Descr>> = c
        .neg
        .iter()
        .filter(|n| n.elems.len() == arity)
        .map(|n| n.elems.iter().map(|ty| cx.descr(ty)).collect())
        .collect();
    if interned_coordinates {
        c.pos[0].elems.iter().any(|ty| cx.coordinate_empty(ty)) || phi_inhabited_tuple(cx, &t, &negs)
    } else {
        phi_tuple(cx, &t, &negs)
    }
}

/// Is the product `∏t` minus the union of the products `∏n` empty?
///
/// Exact, and stated over DESCRIPTORS rather than interned coordinates, so a
/// caller can decide `∏t ⊆ ⋃∏n` for rectangles it built but never interned.
/// Every entry of `n` must have the same arity as `t`; a mismatched arity
/// subtracts nothing and belongs to the caller's filter.
pub(super) fn phi_tuple<'d>(cx: TyCtx<'_>, t: &[&Descr], n: &[impl AsRef<[&'d Descr]>]) -> bool {
    // One empty coordinate empties the whole product — no negation needed.
    t.iter().any(|d| d.is_empty(cx)) || phi_inhabited_tuple(cx, t, n)
}

/// [`phi_tuple`] for a product whose every coordinate is inhabited.
///
/// Each split below keeps that true by construction: a meet is inhabited
/// because the negation is not disjoint from the product on any coordinate,
/// the untouched coordinates are the product's own, and a cut that leaves
/// nothing is answered where it is made. So no coordinate is tested for
/// emptiness twice, and a branch whose cut is empty costs no step.
fn phi_inhabited_tuple<'d>(cx: TyCtx<'_>, t: &[&Descr], n: &[impl AsRef<[&'d Descr]>]) -> bool {
    #[cfg(test)]
    cx.count_tuple_emptiness_step();
    let Some((head, rest)) = n.split_first() else {
        return false;
    };
    let head = head.as_ref();
    // A negation disjoint from the product on any coordinate subtracts
    // nothing: drop it instead of splitting on it.
    if head.iter().zip(t).any(|(h, ti)| ti.is_disjoint(cx, h)) {
        return phi_inhabited_tuple(cx, t, rest);
    }
    // Coordinates before `i` are met with the negation, `i` is cut by it, and
    // the rest are the product's own. Each coordinate's meet is the same for
    // every later `i`, so it is computed once and kept.
    let mut met: Vec<Descr> = Vec::with_capacity(t.len());
    for i in 0..t.len() {
        let cut = t[i].diff(head[i]);
        if !cut.is_empty(cx) {
            let split: Vec<&Descr> = met.iter().chain([&cut]).chain(t[i + 1..].iter().copied()).collect();
            if !phi_inhabited_tuple(cx, &split, rest) {
                return false;
            }
        }
        if i + 1 < t.len() {
            met.push(t[i].intersect(head[i]));
        }
    }
    true
}

/// The positive fold's evidence about one coordinate of the NONEMPTY fragment
/// of a list-clause intersection ("unknown is not none"): before any sig is
/// folded the coordinate is unconstrained -- a distinct state from proven
/// empty. `Empty` absorbs everything folded after it.
enum Evidence<'a> {
    Unconstrained,
    Empty,
    Inhabited(Box<Cow<'a, Descr>>),
}

impl<'a> Evidence<'a> {
    /// Fold one positive sig's constraint on this coordinate. Every
    /// transition is a plain set intersection, so inhabited evidence degrades
    /// to `Empty` only on a genuine set fact.
    fn meet(self, cx: TyCtx<'a>, ty: Ty) -> Self {
        let next = match self {
            Self::Empty => return Self::Empty,
            Self::Unconstrained => Cow::Borrowed(cx.descr(&ty)),
            Self::Inhabited(prev) => Cow::Owned(prev.intersect(cx.descr(&ty))),
        };
        if next.is_empty(cx) {
            Self::Empty
        } else {
            Self::Inhabited(Box::new(next))
        }
    }

    /// The coordinate's descriptor, `top` when nothing constrained it, and
    /// `None` meaning ONLY "proven empty".
    fn fragment(self, top: impl FnOnce() -> Descr) -> Option<Cow<'a, Descr>> {
        match self {
            Self::Unconstrained => Some(Cow::Owned(top())),
            Self::Empty => None,
            Self::Inhabited(d) => Some(*d),
        }
    }
}

/// What a list clause DENOTES, read off its factors once.
///
/// A `ListSig` denotes `[]` (when `empty`) together with every non-empty list
/// whose elements all lie in `elem` and whose terminator lies in `last`, so a
/// whole clause says only two things: does it hold `[]`, and which non-empty
/// lists does it keep. Everything that reads a list clause -- emptiness here,
/// the normal form the persistence boundary writes, the canonical rendering --
/// reads it through this one answer, so none of them can disagree about what a
/// clause means.
pub(crate) struct ListDenotation {
    pub(crate) holds_empty: bool,
    /// The non-empty lists the clause keeps, absent when it keeps none.
    pub(crate) non_empty: Option<NonEmptyLists>,
}

/// Every non-empty list over `elem` ending in `last`, except those that lie
/// in one of `minus`.
///
/// A subtraction whose elements cover `elem` has already been taken out of
/// `last`: removing every list over `elem` that ends in `N` is ending
/// somewhere outside `N`. What is left in `minus` are the subtractions over a
/// smaller element, each met with `elem` and `last`, which is exact and is
/// what makes a subtraction that removes nothing recognizable.
pub(crate) struct NonEmptyLists {
    pub(crate) elem: Descr,
    pub(crate) last: Descr,
    pub(crate) minus: Vec<ConsCut>,
}

/// One subtraction from a list clause's non-empty fragment: every non-empty
/// list over `elem` ending in `last`.
#[derive(PartialEq)]
pub(crate) struct ConsCut {
    pub(crate) elem: Descr,
    pub(crate) last: Descr,
}

/// Whether a list clause holds `[]`, read off the `empty` flags alone.
///
/// `[]` is in every positive that carries the flag and in no negative that
/// does, which is the whole rule: it touches no element, so it is the same
/// answer before and after a substitution, and the axis merge across a clause
/// set may ask it without a `TyCtx`.
pub(super) fn clause_holds_empty(c: &Conj<ListSig>) -> bool {
    c.pos.iter().all(|p| p.empty) && !c.neg.iter().any(|n| n.empty)
}

/// The non-empty fragment the positives keep before any subtraction: the
/// meet of their elements and the meet of their terminators. `None` when it
/// is empty, which a positive that holds only `[]` forces.
fn positive_fragment<'a>(cx: TyCtx<'a>, c: &Conj<ListSig>) -> Option<(Cow<'a, Descr>, Cow<'a, Descr>)> {
    let mut elem = Evidence::Unconstrained;
    let mut last = Evidence::Unconstrained;
    for p in &c.pos {
        let cons = p.cons?;
        elem = elem.meet(cx, cons.elem);
        last = last.meet(cx, cons.last);
    }
    Some((elem.fragment(Descr::any)?, last.fragment(Descr::any_terminator)?))
}

/// The terminators left once every subtraction whose elements cover `elem`
/// has taken its own out, or `None` when none is left.
///
/// That is the whole emptiness rule. A list escapes a subtraction over a
/// smaller element by holding one element outside it, and one list can hold
/// such an element for every such subtraction at once; a subtraction that
/// covers `elem` it escapes only by ending outside it.
fn surviving_terminators<'a>(
    cx: TyCtx<'_>,
    c: &Conj<ListSig>,
    elem: &Descr,
    last: Cow<'a, Descr>,
) -> Option<Cow<'a, Descr>> {
    let mut last = last;
    for cut in c.neg.iter().filter_map(|n| n.cons) {
        if elem.diff(cx.descr(&cut.elem)).is_empty(cx) {
            last = Cow::Owned(last.diff(cx.descr(&cut.last)));
        }
    }
    (!last.is_empty(cx)).then_some(last)
}

/// `None` when the clause denotes nothing.
pub(crate) fn list_denotation(cx: TyCtx<'_>, c: &Conj<ListSig>) -> Option<ListDenotation> {
    let holds_empty = clause_holds_empty(c);
    let just_empty = || {
        holds_empty.then_some(ListDenotation {
            holds_empty: true,
            non_empty: None,
        })
    };
    let Some((elem, last)) = positive_fragment(cx, c) else {
        return just_empty();
    };
    let Some(last) = surviving_terminators(cx, c, &elem, last) else {
        return just_empty();
    };
    let mut minus: Vec<ConsCut> = Vec::new();
    for n in c.neg.iter().filter_map(|n| n.cons) {
        let cut_elem = elem.intersect(cx.descr(&n.elem));
        if cut_elem.is_empty(cx) || elem.diff(&cut_elem).is_empty(cx) {
            continue;
        }
        let cut_last = last.intersect(cx.descr(&n.last));
        if cut_last.is_empty(cx) {
            continue;
        }
        let cut = ConsCut {
            elem: cut_elem,
            last: cut_last,
        };
        if !minus.contains(&cut) {
            minus.push(cut);
        }
    }
    Some(ListDenotation {
        holds_empty,
        non_empty: Some(NonEmptyLists {
            elem: elem.into_owned(),
            last: last.into_owned(),
            minus,
        }),
    })
}

/// Whether a list clause denotes nothing: it holds no `[]` and no non-empty
/// list. This is [`list_denotation`] being absent, decided without building
/// the denotation's subtractions.
pub(crate) fn list_clause_empty(cx: TyCtx<'_>, c: &Conj<ListSig>) -> bool {
    if clause_holds_empty(c) {
        return false;
    }
    let Some((elem, last)) = positive_fragment(cx, c) else {
        return true;
    };
    surviving_terminators(cx, c, &elem, last).is_none()
}

pub(crate) fn resource_clause_empty(cx: TyCtx<'_>, c: &Conj<ResourceSig>) -> bool {
    let mut payload = match c.pos.first() {
        Some(first) => Cow::Borrowed(cx.descr(&first.payload)),
        None => Cow::Owned(Descr::any()),
    };
    for p in c.pos.iter().skip(1) {
        payload = Cow::Owned(payload.intersect(cx.descr(&p.payload)));
    }
    if !c.pos.is_empty() && payload.is_empty(cx) {
        return true;
    }
    if c.neg.is_empty() {
        return false;
    }
    c.neg.iter().any(|n| payload.diff(cx.descr(&n.payload)).is_empty(cx))
}

fn arrow_input(sig: &ArrowSig) -> Descr {
    Descr::tuple_of(sig.args.clone())
}

/// Whether two closure literals can name ONE value: the same brand, or either
/// one anonymous — an anonymous literal is every brand at once.
fn closure_brands_meet(a: Option<FnId>, b: Option<FnId>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a == b,
        _ => true,
    }
}

/// Whether every brand `pos` names, `neg` names too. An anonymous `neg`
/// subtracts every brand; a branded `neg` subtracts only its own, and never
/// covers an anonymous `pos`, which names every other brand as well.
fn closure_brand_inside(pos: Option<FnId>, neg: Option<FnId>) -> bool {
    match (pos, neg) {
        (_, None) => true,
        (Some(pos), Some(neg)) => pos == neg,
        (None, Some(_)) => false,
    }
}

pub(crate) fn func_clause_empty(cx: TyCtx<'_>, c: &Conj<ArrowSig>) -> bool {
    let p = &c.pos;
    let n = &c.neg;

    // A function takes one number of arguments, so arrows of different
    // arities share no function.
    let arity = p.first().map(|sig| sig.args.len());
    if p.iter().any(|sig| Some(sig.args.len()) != arity) {
        return true;
    }

    let pos_lits: Vec<&ClosureLit> = p.iter().filter_map(|s| s.lit.as_ref()).collect();
    // A closure holds exactly one value per capture slot, so a literal whose
    // capture TYPE is empty denotes nothing -- however it got that way. An
    // anonymous literal is every brand at once, so it MERGES with a branded
    // one instead of staying distinct from it, and the merged literal's
    // capture is the two captures' intersection; one brand at two capture
    // types merges the same way. Asking each literal about its own captures
    // covers both, where the pairwise loop below can only see pairs that
    // survived the merge.
    if pos_lits
        .iter()
        .any(|lit| lit.captures.iter().any(|c| cx.descr(c).is_empty(cx)))
    {
        return true;
    }
    for i in 0..pos_lits.len() {
        for j in (i + 1)..pos_lits.len() {
            if !closure_brands_meet(pos_lits[i].fn_id, pos_lits[j].fn_id)
                || pos_lits[i].captures.len() != pos_lits[j].captures.len()
            {
                return true;
            }
            for (a, b) in pos_lits[i].captures.iter().zip(&pos_lits[j].captures) {
                if cx.descr(a).intersect(cx.descr(b)).is_empty(cx) {
                    return true;
                }
            }
        }
    }

    'next_neg_lit: for negj in n {
        let Some(neg_lit) = &negj.lit else {
            continue;
        };
        let mut found_matching_pos = false;
        for posi in p {
            let Some(pos_lit) = &posi.lit else {
                continue;
            };
            if !closure_brand_inside(pos_lit.fn_id, neg_lit.fn_id) || pos_lit.captures.len() != neg_lit.captures.len() {
                continue;
            }
            found_matching_pos = true;
            // The clause is empty only when the positive capture space is
            // fully covered by the negated capture space: P \ N = empty iff
            // P ⊆ N.
            let pos_subset_of_neg = pos_lit
                .captures
                .iter()
                .zip(&neg_lit.captures)
                .all(|(pc, nc)| cx.descr(pc).diff(cx.descr(nc)).is_empty(cx));
            if pos_subset_of_neg {
                return true;
            }
        }
        if found_matching_pos {
            continue 'next_neg_lit;
        }
    }

    // An arrow takes away functions of its own arity only, so a clause that
    // states no arity keeps the functions of every other one.
    let Some(arity) = arity else {
        return false;
    };
    let mut plain_negs = n
        .iter()
        .filter(|negj| negj.lit.is_none() && negj.args.len() == arity)
        .peekable();
    if plain_negs.peek().is_none() {
        return false;
    }
    let n_pos = p.len();
    let pos_inputs: Vec<Descr> = p.iter().map(arrow_input).collect();
    'next_neg: for negj in plain_negs {
        let s = arrow_input(negj);
        let v = cx.descr(&negj.ret);
        for mask in 0u32..(1u32 << n_pos) {
            let mut union_in = Descr::none();
            let mut inter_out = Descr::any();
            for (i, pi) in p.iter().enumerate().take(n_pos) {
                if (mask >> i) & 1 == 1 {
                    union_in = union_in.union(cx, &pos_inputs[i]);
                } else {
                    inter_out = inter_out.intersect(cx.descr(&pi.ret));
                }
            }
            if s.diff(&union_in).is_empty(cx) {
                continue;
            }
            if inter_out.diff(v).is_empty(cx) {
                continue;
            }
            continue 'next_neg;
        }
        return true;
    }
    false
}

/// A map clause: the maps every positive signature admits and no negative
/// signature does.
///
/// Following Elixir's `map_line_empty?`, a negative removes from the line
/// exactly what it constrains: at each key either signature names, the line
/// keeps what the negative does not hold there, and the clause is empty when
/// every such remainder is empty against the negatives still to come. A
/// negative whose domain admits less than the line's somewhere removes
/// nothing a key of that kind could not escape: the kinds are infinite, so a
/// fresh key of that kind exists whose value the negative rejects, and the
/// line keeps a map holding it.
pub(crate) fn map_clause_empty(cx: TyCtx<'_>, c: &Conj<MapSig>) -> bool {
    let Some((first, rest)) = c.pos.split_first() else {
        return false;
    };
    if c.neg.is_empty() && rest.is_empty() {
        return first
            .fields
            .values()
            .any(|field| !field.optional && cx.descr(&field.ty).is_empty(cx));
    }
    let mut line = MapLine::of(cx, first);
    for sig in rest {
        line.meet(cx, sig);
    }
    line.has_empty_required_field(cx) || map_line_empty(cx, &line, &c.neg)
}

/// The meet of a clause's positive signatures, as descriptors.
#[derive(Clone)]
struct MapLine {
    fields: BTreeMap<MapKey, LineField>,
    domains: Vec<Descr>,
}

#[derive(Clone)]
struct LineField {
    ty: Descr,
    optional: bool,
}

impl LineField {
    fn of(cx: TyCtx<'_>, field: MapField) -> Self {
        Self {
            ty: cx.descr(&field.ty).clone(),
            optional: field.optional,
        }
    }
}

impl MapLine {
    fn of(cx: TyCtx<'_>, sig: &MapSig) -> Self {
        Self {
            fields: sig
                .fields
                .iter()
                .map(|(key, field)| (key.clone(), LineField::of(cx, *field)))
                .collect(),
            domains: sig.domains.tys().map(|ty| cx.descr(&ty).clone()).collect(),
        }
    }

    fn field_at(&self, key: &MapKey) -> LineField {
        self.fields.get(key).cloned().unwrap_or_else(|| LineField {
            ty: self.domains[MapDomain::of_key(key) as usize].clone(),
            optional: true,
        })
    }

    fn meet(&mut self, cx: TyCtx<'_>, sig: &MapSig) {
        let keys: BTreeSet<MapKey> = self.fields.keys().chain(sig.fields.keys()).cloned().collect();
        for key in keys {
            let ours = self.field_at(&key);
            let theirs = LineField::of(cx, sig.field_at(&key));
            self.fields.insert(
                key,
                LineField {
                    ty: ours.ty.intersect(&theirs.ty),
                    optional: ours.optional && theirs.optional,
                },
            );
        }
        for (domain, ty) in sig.domains.iter() {
            let slot = &mut self.domains[domain as usize];
            *slot = slot.intersect(cx.descr(&ty));
        }
    }

    fn has_empty_required_field(&self, cx: TyCtx<'_>) -> bool {
        self.fields
            .values()
            .any(|field| !field.optional && field.ty.is_empty(cx))
    }

    /// Whether every key kind the line allows, the negative allows too.
    fn domains_within(&self, cx: TyCtx<'_>, negative: &MapSig) -> bool {
        negative
            .domains
            .iter()
            .all(|(domain, ty)| self.domains[domain as usize].is_subtype(cx, cx.descr(&ty)))
    }
}

fn map_line_empty(cx: TyCtx<'_>, line: &MapLine, negatives: &[MapSig]) -> bool {
    let Some((negative, rest)) = negatives.split_first() else {
        return false;
    };
    if !line.domains_within(cx, negative) {
        return map_line_empty(cx, line, rest);
    }
    let keys: BTreeSet<&MapKey> = line.fields.keys().chain(negative.fields.keys()).collect();
    keys.into_iter().all(|key| {
        let ours = line.field_at(key);
        let theirs = negative.field_at(key);
        let remainder = LineField {
            ty: ours.ty.diff(cx.descr(&theirs.ty)),
            optional: ours.optional && !theirs.optional,
        };
        if !remainder.optional && remainder.ty.is_empty(cx) {
            return true;
        }
        let mut next = line.clone();
        next.fields.insert(key.clone(), remainder);
        map_line_empty(cx, &next, rest)
    })
}

#[cfg(test)]
#[path = "emptiness_test.rs"]
mod emptiness_test;
