//! The canonical external form of a type: comparison-only, id-free, faithful.
//!
//! `Ty` is an arena index in one `World`. Across two worlds it carries no
//! meaning, so nothing durable may compare ids. This module renders a type as
//! ordered structural text instead, with the contract
//!
//! ```text
//! canon(a) == canon(b)   iff   a and b are mutually subtype
//! ```
//!
//! The "only if" half is by construction: every normalization step below
//! rewrites a descriptor to a semantically EQUAL one, and the rendering is a
//! function of the normalized form. The "if" half is a measured property, held
//! by the faithfulness ratchet in `compiler2::canon_test`.
//!
//! `Types::display` cannot serve: it is not injective. It renders the
//! possibly-empty and the non-empty list identically as `[T]`, and it collapses
//! each axis's saturated clause onto the bare word `any`. A false equivalence
//! is far worse than a false difference for an equivalence oracle, so this
//! rendering distinguishes every form the lattice does.
//!
//! Normalization runs on DESCRIPTORS, not only on interned `Ty`s: tuple
//! coordinate widening builds descriptors that were never interned, and
//! interning them here would mutate the very arena the canon describes.

use std::collections::HashMap;
use std::sync::Arc;

use crate::finite_set::FiniteSet;
use crate::fz_ir::FnId;

use super::bits::{BASIC_NAMES, BasicBits};
use super::conj::Conj;
use super::descr::Descr;
use super::emptiness::{self, Memo};
use super::format::brand_refinement;
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, ResourceSig, TupleSig};
use super::{CallableValueKind, MapKey, Ty, TyCtx, TypeVarId, Types};

/// Renders types in their canonical external form, memoized by `Ty`.
///
/// A compile mints ~1.4k distinct types against ~17.5k events, so the cost is
/// per distinct type rather than per rendering site. Build one per comparison
/// session and thread it.
pub(crate) struct TyCanon<'a> {
    /// Resolves a closure literal's `FnId` to a stable label. A raw `fn_id` is
    /// a mint-order index, so it can never be the rendered identity; the owner
    /// (`World`) knows the module/name/arity behind it.
    labels: &'a dyn Fn(FnId) -> String,
    bodies: HashMap<Ty, Arc<str>>,
    fingerprints: HashMap<Ty, Arc<str>>,
    whole: HashMap<Ty, Arc<str>>,
}

impl<'a> TyCanon<'a> {
    pub(crate) fn new(labels: &'a dyn Fn(FnId) -> String) -> Self {
        Self {
            labels,
            bodies: HashMap::new(),
            fingerprints: HashMap::new(),
            whole: HashMap::new(),
        }
    }

    /// The canonical form of `ty`: an invariant fingerprint, then the ordered
    /// structural body.
    pub(crate) fn render(&mut self, types: &Types, ty: Ty) -> Arc<str> {
        if let Some(hit) = self.whole.get(&ty) {
            return Arc::clone(hit);
        }
        let cx = types.ctx();
        let text: Arc<str> = format!("{} {}", self.fingerprint_at(cx, ty), self.body(cx, ty)).into();
        self.whole.insert(ty, Arc::clone(&text));
        text
    }

    /// The fingerprint alone — the grouping key the faithfulness ratchet needs
    /// to avoid comparing every arena type against every other. Equivalent
    /// types always share it, so types in different groups are inequivalent by
    /// construction.
    #[cfg(test)]
    pub(crate) fn fingerprint(&mut self, types: &Types, ty: Ty) -> Arc<str> {
        self.fingerprint_at(types.ctx(), ty)
    }

    /// One type variable, rendered the way the arrow language names it: a
    /// structural address (`a0`, `a1_0`, `r0`) when the id carries the address
    /// tag, else the free var's own id.
    pub(crate) fn var(&self, types: &Types, id: TypeVarId) -> String {
        types.ctx().render_var(id)
    }

    fn fingerprint_at(&mut self, cx: TyCtx<'_>, ty: Ty) -> Arc<str> {
        if let Some(hit) = self.fingerprints.get(&ty) {
            return Arc::clone(hit);
        }
        let text: Arc<str> = descr_fingerprint(cx, cx.descr(&ty)).into();
        self.fingerprints.insert(ty, Arc::clone(&text));
        text
    }

    fn body(&mut self, cx: TyCtx<'_>, ty: Ty) -> Arc<str> {
        if let Some(hit) = self.bodies.get(&ty) {
            return Arc::clone(hit);
        }
        let text: Arc<str> = self.descr_body(cx, cx.descr(&ty)).into();
        self.bodies.insert(ty, Arc::clone(&text));
        text
    }

    // ------------------------------------------------------------------
    // Body
    // ------------------------------------------------------------------

    fn descr_body(&mut self, cx: TyCtx<'_>, d: &Descr) -> String {
        if d.is_empty_memo(cx, &mut Memo::default()) {
            return "none".to_string();
        }
        if is_full(cx, d) {
            return "any".to_string();
        }
        let axes = self.axes(cx, d);
        let mut parts: Vec<String> = basic_names(d.basic);
        push_set(&mut parts, &d.atoms, "atom", |name| format!(":{name}"));
        push_set(&mut parts, &d.opaques, "opaque", Clone::clone);
        push_set(&mut parts, &d.vars, "var", |id| cx.render_var(*id));
        parts.extend(sorted(axes.tuple_rects.iter().map(|rect| self.rect_text(cx, rect))));
        parts.extend(sorted(
            self.clause_texts(cx, &axes.tuple_complex, Self::tuple_clause)
                .into_iter(),
        ));
        parts.extend(sorted(
            self.clause_texts(cx, &axes.lists, Self::list_clause).into_iter(),
        ));
        parts.extend(sorted(
            self.clause_texts(cx, &axes.resources, Self::resource_clause)
                .into_iter(),
        ));
        parts.extend(sorted(
            self.clause_texts(cx, &axes.funcs, Self::func_clause).into_iter(),
        ));
        parts.extend(sorted(self.clause_texts(cx, &axes.maps, Self::map_clause).into_iter()));
        brand_refinement(&d.brands, parts.join(" | "))
    }

    fn rect_text(&mut self, cx: TyCtx<'_>, rect: &Rect) -> String {
        let coords: Vec<String> = rect.iter().map(|coord| self.coord_text(cx, coord)).collect();
        format!("{{{}}}", coords.join(", "))
    }

    fn coord_text(&mut self, cx: TyCtx<'_>, coord: &Coord) -> String {
        match coord {
            Coord::Interned(ty) => self.body(cx, *ty).to_string(),
            Coord::Widened(d) => self.descr_body(cx, d),
        }
    }

    /// One clause rendered with its factors sorted. `top` names the saturated
    /// clause (`Conj::top()`) — "every tuple", "every list", and so on.
    /// `display` collapses all five of those onto the bare word `any`, which is
    /// exactly the conflation this rendering must not repeat.
    fn conj_text<T>(
        &mut self,
        cx: TyCtx<'_>,
        c: &Conj<T>,
        sig: fn(&mut Self, TyCtx<'_>, &T) -> String,
        top: &str,
    ) -> String {
        if c.pos.is_empty() && c.neg.is_empty() {
            return top.to_string();
        }
        let mut factors: Vec<String> = c.pos.iter().map(|p| sig(self, cx, p)).collect();
        factors.extend(c.neg.iter().map(|n| format!("not({})", sig(self, cx, n))));
        factors.sort();
        factors.join(" & ")
    }

    fn tuple_clause(&mut self, cx: TyCtx<'_>, c: &Conj<TupleSig>) -> String {
        self.conj_text(cx, c, Self::tuple_sig, "tuple")
    }

    /// A list clause rendered from what it DENOTES, not from the factors it was
    /// built out of.
    ///
    /// A `ListSig` denotes `{[]}` (when `empty`) together with every list whose
    /// elements all lie in `elem`, so a clause is fully described by two facts:
    /// does it hold `[]`, and what is its non-empty fragment's element type.
    /// Factor-by-factor rendering would keep `list(T) & not([])` and
    /// `non_empty_list(T)` apart, and they are one type.
    ///
    /// A negated sig with no element denotes `{[]}` or `∅`, so it can only
    /// remove `[]`. A negated sig whose element covers the whole fragment
    /// removes the fragment outright. Anything else subtracts only part of the
    /// fragment and survives as a residual factor — rendered without its own
    /// `empty` flag, which by then cannot matter.
    fn list_clause(&mut self, cx: TyCtx<'_>, c: &Conj<ListSig>) -> String {
        if c.pos.is_empty() && c.neg.is_empty() {
            return "list".to_string();
        }
        let holds_empty = c.pos.iter().all(|p| p.empty) && !c.neg.iter().any(|n| n.empty);
        let mut fragment = Some(Descr::any());
        for p in &c.pos {
            fragment = match (fragment, p.elem) {
                (Some(f), Some(e)) => Some(f.intersect(cx.descr(&e))),
                _ => None,
            };
        }
        if fragment
            .as_ref()
            .is_some_and(|f| f.is_empty_memo(cx, &mut Memo::default()))
        {
            fragment = None;
        }
        let covered = |f: &Descr, elem: &Ty| f.diff(cx.descr(elem)).is_empty_memo(cx, &mut Memo::default());
        let erased = fragment
            .as_ref()
            .is_none_or(|f| c.neg.iter().any(|n| n.elem.is_some_and(|e| covered(f, &e))));
        let mut factors = vec![match (&fragment, erased, holds_empty) {
            (_, true, true) => "empty_list()".to_string(),
            (_, true, false) => "none".to_string(),
            (Some(f), false, true) => format!("list({})", self.descr_body(cx, f)),
            (Some(f), false, false) => format!("non_empty_list({})", self.descr_body(cx, f)),
            (None, false, _) => unreachable!("an absent fragment is always erased"),
        }];
        if !erased {
            factors.extend(sorted(c.neg.iter().filter_map(|n| n.elem).map(|elem| {
                let rendered = self.body(cx, elem);
                format!("not(non_empty_list({rendered}))")
            })));
        }
        factors.join(" & ")
    }

    fn resource_clause(&mut self, cx: TyCtx<'_>, c: &Conj<ResourceSig>) -> String {
        self.conj_text(cx, c, Self::resource_sig, "resource")
    }

    fn map_clause(&mut self, cx: TyCtx<'_>, c: &Conj<MapSig>) -> String {
        self.conj_text(cx, c, Self::map_sig, "map")
    }

    /// A closure literal standing alone in its clause denotes ONE callable
    /// VALUE, and `func_clause_empty` decides `{v} \ {w}` from `fn_id` and the
    /// captures alone. The arrow surface the clause also carries is metadata
    /// about that value, not part of its identity, so two surfaces over one
    /// closure are one type and have to reach one rendering.
    fn func_clause(&mut self, cx: TyCtx<'_>, c: &Conj<ArrowSig>) -> String {
        if let ([sig], []) = (c.pos.as_slice(), c.neg.as_slice())
            && let Some(lit) = &sig.lit
        {
            return self.closure_lit(cx, lit);
        }
        self.conj_text(cx, c, Self::arrow_sig, "fun")
    }

    fn tuple_sig(&mut self, cx: TyCtx<'_>, sig: &TupleSig) -> String {
        let elems: Vec<String> = sig.elems.iter().map(|ty| self.body(cx, *ty).to_string()).collect();
        format!("{{{}}}", elems.join(", "))
    }

    fn resource_sig(&mut self, cx: TyCtx<'_>, sig: &ResourceSig) -> String {
        format!("resource({})", self.body(cx, sig.payload))
    }

    fn arrow_sig(&mut self, cx: TyCtx<'_>, sig: &ArrowSig) -> String {
        let args: Vec<String> = sig.args.iter().map(|ty| self.body(cx, *ty).to_string()).collect();
        let base = format!("({}) -> {}", args.join(", "), self.body(cx, sig.ret));
        match &sig.lit {
            None => base,
            Some(lit) => format!("{base} {}", self.closure_lit(cx, lit)),
        }
    }

    /// `fnref[label]` for a bare function reference, `closure[label](caps)`
    /// for an env-carrying closure. The label is `?` for an ANONYMOUS literal
    /// -- a closure of some function over exactly these capture types, which
    /// is what a forwarder key leaves of a literal whose brand it erased.
    /// `closure[?](int)` and `closure[?](float)` are two forms because the
    /// capture types are two, and `closure[?](int)` and `closure[L](int)` are
    /// two because the anonymous one names every brand and `L` names one.
    ///
    /// `closure[?]` is the only anonymous form. `fnref[?]` is not a form at
    /// all: a `FnRef` literal carries no captures (`Types::fn_ref_lit` is its
    /// only constructor), and the erasure drops a capture-free literal whole
    /// rather than anonymising it -- there is nothing left to say once the
    /// brand is gone -- so a `FnRef` literal always keeps its label.
    fn closure_lit(&mut self, cx: TyCtx<'_>, lit: &ClosureLit) -> String {
        let label = match lit.fn_id {
            Some(fn_id) => (self.labels)(fn_id),
            None => "?".into(),
        };
        match lit.kind {
            CallableValueKind::FnRef => format!("fnref[{label}]"),
            CallableValueKind::Closure => {
                let caps: Vec<String> = lit.captures.iter().map(|ty| self.body(cx, *ty).to_string()).collect();
                format!("closure[{label}]({})", caps.join(", "))
            }
        }
    }

    fn map_sig(&mut self, cx: TyCtx<'_>, sig: &MapSig) -> String {
        let fields: Vec<String> = sig
            .fields
            .iter()
            .map(|(key, value)| format!("{} => {}", map_key(key), self.body(cx, *value)))
            .collect();
        format!("%{{{}}}", fields.join(", "))
    }

    // ------------------------------------------------------------------
    // Normalization
    // ------------------------------------------------------------------

    fn axes(&mut self, cx: TyCtx<'_>, d: &Descr) -> Axes {
        let tuples = saturate(
            cx,
            drop_empty(cx, &d.tuples, emptiness::tuple_clause_empty),
            |d, clauses| d.tuples = clauses,
        );
        let (mut tuple_rects, tuple_complex) = split_rects(tuples);
        widen_rects(cx, &mut tuple_rects);
        let rect_keys = tuple_rects.iter().map(|rect| self.rect_text(cx, rect)).collect();
        let tuple_rects = drop_subsumed_rects(cx, tuple_rects, rect_keys);

        let lists = saturate(
            cx,
            drop_empty(cx, &d.lists, emptiness::list_clause_empty),
            |d, clauses| d.lists = clauses,
        );
        let keys = self.clause_texts(cx, &lists, Self::list_clause);
        let lists = drop_subsumed(cx, lists, keys, |d, clauses| d.lists = clauses);

        let resources = saturate(
            cx,
            drop_empty(cx, &d.resources, emptiness::resource_clause_empty),
            |d, clauses| d.resources = clauses,
        );
        let keys = self.clause_texts(cx, &resources, Self::resource_clause);
        let resources = drop_subsumed(cx, resources, keys, |d, clauses| d.resources = clauses);

        let funcs = saturate(
            cx,
            drop_empty(cx, &d.funcs, emptiness::func_clause_empty),
            |d, clauses| d.funcs = clauses,
        );
        let keys = self.clause_texts(cx, &funcs, Self::func_clause);
        let funcs = drop_subsumed(cx, funcs, keys, |d, clauses| d.funcs = clauses);

        let maps = saturate(
            cx,
            drop_empty(cx, &d.maps, emptiness::map_clause_empty),
            |d, clauses| d.maps = clauses,
        );
        let keys = self.clause_texts(cx, &maps, Self::map_clause);
        let maps = drop_subsumed(cx, maps, keys, |d, clauses| d.maps = clauses);

        Axes {
            tuple_rects,
            tuple_complex,
            lists,
            resources,
            funcs,
            maps,
        }
    }

    /// One axis's clauses rendered, POSITIONALLY. The drop order keys on these,
    /// so they must stay aligned with the clause vector; sorting happens where
    /// the texts are emitted, not here.
    fn clause_texts<T>(
        &mut self,
        cx: TyCtx<'_>,
        clauses: &[Conj<T>],
        clause: fn(&mut Self, TyCtx<'_>, &Conj<T>) -> String,
    ) -> Vec<String> {
        clauses.iter().map(|c| clause(self, cx, c)).collect()
    }
}

// ----------------------------------------------------------------------
// Normalized axes
// ----------------------------------------------------------------------

/// One tuple coordinate. Widening replaces an interned coordinate with a
/// descriptor that was never interned, so the two cases have to coexist.
enum Coord {
    Interned(Ty),
    Widened(Box<Descr>),
}

impl Coord {
    fn descr(&self, cx: TyCtx<'_>) -> Descr {
        match self {
            Self::Interned(ty) => cx.descr(ty).clone(),
            Self::Widened(d) => (**d).clone(),
        }
    }
}

/// A plain single-positive tuple clause: a rectangle `∏ coords`.
type Rect = Vec<Coord>;

/// The per-axis DNFs after normalization.
struct Axes {
    tuple_rects: Vec<Rect>,
    tuple_complex: Vec<Conj<TupleSig>>,
    lists: Vec<Conj<ListSig>>,
    resources: Vec<Conj<ResourceSig>>,
    funcs: Vec<Conj<ArrowSig>>,
    maps: Vec<Conj<MapSig>>,
}

fn drop_empty<T: Clone>(
    cx: TyCtx<'_>,
    clauses: &[Conj<T>],
    is_empty: fn(TyCtx<'_>, &Conj<T>, &mut Memo) -> bool,
) -> Vec<Conj<T>> {
    clauses
        .iter()
        .filter(|c| !is_empty(cx, c, &mut Memo::default()))
        .cloned()
        .collect()
}

/// Collapse an axis whose clauses already cover the whole axis to that axis's
/// saturated clause.
///
/// The lattice reaches saturation through ordinary clauses: `(X) -> any`
/// constrains nothing (`f(X) ⊆ any` holds for every function), so it denotes
/// EVERY callable whatever `X` is. Without this step the same set would render
/// once per `X` the arena happened to mint.
fn saturate<T: Clone>(cx: TyCtx<'_>, clauses: Vec<Conj<T>>, install: fn(&mut Descr, Vec<Conj<T>>)) -> Vec<Conj<T>> {
    if clauses.is_empty() || matches!(clauses.as_slice(), [c] if c.pos.is_empty() && c.neg.is_empty()) {
        return clauses;
    }
    let mut mine = Descr::unbranded();
    install(&mut mine, clauses.clone());
    let mut top = Descr::unbranded();
    install(&mut top, vec![Conj::top()]);
    if top.is_subtype(cx, &mine) {
        return vec![Conj::top()];
    }
    clauses
}

fn split_rects(clauses: Vec<Conj<TupleSig>>) -> (Vec<Rect>, Vec<Conj<TupleSig>>) {
    let mut rects = Vec::new();
    let mut complex = Vec::new();
    for c in clauses {
        match (c.pos.as_slice(), c.neg.as_slice()) {
            ([sig], []) => rects.push(sig.elems.iter().copied().map(Coord::Interned).collect()),
            _ => complex.push(c),
        }
    }
    (rects, complex)
}

/// Widen each rectangle's coordinates to the axis fixpoint.
///
/// Two decompositions of one tuple union differ by where they carved the
/// overlap. `{list(int), []} | {[], non_empty_list(int)}` and
/// `{list(int), []} | {[], list(int)}` denote the same set: the extra point
/// `{[], []}` the second admits is already covered by the FIRST clause. No
/// pairwise clause subsumption can see that — neither clause contains the other
/// — so the axis needs a rewrite that both decompositions reach.
///
/// Widening is it: replace coordinate `k` of one rectangle with the union of
/// coordinate `k` over every same-arity rectangle, and keep the replacement
/// only if the widened rectangle is still contained in the axis union. Every
/// accepted step preserves the denoted set exactly — a rectangle only grows,
/// and never past the union — so the union is invariant across the whole loop.
/// That is also why the result cannot depend on the order steps are taken in,
/// and why each (rectangle, coordinate) widens at most once: its target is that
/// one fixed union.
fn widen_rects(cx: TyCtx<'_>, rects: &mut [Rect]) {
    loop {
        let mats: Vec<Vec<Descr>> = rects
            .iter()
            .map(|rect| rect.iter().map(|coord| coord.descr(cx)).collect())
            .collect();
        let Some((index, coord, widened)) = next_widening(cx, &mats) else {
            return;
        };
        rects[index][coord] = Coord::Widened(Box::new(widened));
    }
}

fn next_widening(cx: TyCtx<'_>, mats: &[Vec<Descr>]) -> Option<(usize, usize, Descr)> {
    for (index, rect) in mats.iter().enumerate() {
        let arity = rect.len();
        let siblings: Vec<&Vec<Descr>> = mats.iter().filter(|other| other.len() == arity).collect();
        for coord in 0..arity {
            let candidate = siblings
                .iter()
                .fold(Descr::none(), |acc, sibling| acc.union(cx, &sibling[coord]));
            if candidate == rect[coord] {
                continue;
            }
            let mut trial = rect.clone();
            trial[coord] = candidate.clone();
            let cover: Vec<Vec<Descr>> = siblings.iter().map(|sibling| (*sibling).clone()).collect();
            if emptiness::phi_tuple(cx, &trial, &cover, &mut Memo::default()) {
                return Some((index, coord, candidate));
            }
        }
    }
    None
}

/// Drop every rectangle covered by the union of the ones that survive.
///
/// Rectangles are visited in rendered-key order, so the outcome depends on the
/// rectangle SET and not on the arena order the clauses happened to be minted
/// in. Exact duplicates leave exactly one survivor: once the first is dropped
/// it stops covering its twin.
fn drop_subsumed_rects(cx: TyCtx<'_>, rects: Vec<Rect>, keys: Vec<String>) -> Vec<Rect> {
    if rects.len() < 2 {
        return rects;
    }
    let mats: Vec<Vec<Descr>> = rects
        .iter()
        .map(|rect| rect.iter().map(|coord| coord.descr(cx)).collect())
        .collect();
    let mut keep = vec![true; rects.len()];
    for index in visit_order(keys) {
        let arity = mats[index].len();
        let cover: Vec<Vec<Descr>> = (0..mats.len())
            .filter(|other| *other != index && keep[*other] && mats[*other].len() == arity)
            .map(|other| mats[other].clone())
            .collect();
        if emptiness::phi_tuple(cx, &mats[index], &cover, &mut Memo::default()) {
            keep[index] = false;
        }
    }
    retain_kept(rects, keep)
}

/// The single-axis form of the same rule for the axes that need no widening: a
/// clause covered by the union of the surviving clauses on its own axis adds
/// nothing and is dropped.
fn drop_subsumed<T: Clone>(
    cx: TyCtx<'_>,
    clauses: Vec<Conj<T>>,
    keys: Vec<String>,
    install: fn(&mut Descr, Vec<Conj<T>>),
) -> Vec<Conj<T>> {
    if clauses.len() < 2 {
        return clauses;
    }
    let mut keep = vec![true; clauses.len()];
    for index in visit_order(keys) {
        let others: Vec<Conj<T>> = (0..clauses.len())
            .filter(|other| *other != index && keep[*other])
            .map(|other| clauses[other].clone())
            .collect();
        if others.is_empty() {
            continue;
        }
        let mut mine = Descr::unbranded();
        install(&mut mine, vec![clauses[index].clone()]);
        let mut rest = Descr::unbranded();
        install(&mut rest, others);
        if mine.is_subtype(cx, &rest) {
            keep[index] = false;
        }
    }
    retain_kept(clauses, keep)
}

fn visit_order(keys: Vec<String>) -> Vec<usize> {
    let mut order: Vec<usize> = (0..keys.len()).collect();
    order.sort_by(|left, right| keys[*left].cmp(&keys[*right]).then(left.cmp(right)));
    order
}

fn retain_kept<T>(items: Vec<T>, keep: Vec<bool>) -> Vec<T> {
    items
        .into_iter()
        .zip(keep)
        .filter_map(|(item, keep)| keep.then_some(item))
        .collect()
}

// ----------------------------------------------------------------------
// Shared rendering helpers
// ----------------------------------------------------------------------

/// Every component here is provably invariant under type equivalence.
///
/// The KIND axes are independent: membership on one is decided by that axis
/// alone (`Descr::intersect`/`diff` are pointwise and a descriptor is empty
/// when every kind axis is). So `a ≡ b` forces `a \ b = ∅` on each axis
/// separately, which for the scalar axes means equal `BasicBits` and equal
/// finite/cofinite sets — their universes are infinite, so a finite set never
/// denotes what a cofinite one does. `brands` is not a kind but a REFINEMENT
/// factor over all of them, so it is recorded the same way and read the same
/// way, with the unconstrained slot (the unbranded case) omitted.
///
/// For the structural axes only INHABITED-ness survives: clause counts do not,
/// since the whole point of the normalization elsewhere in this module is that
/// two clause sets can denote one type. Nothing finer is recorded — a clause
/// count, a clause arity, or a negated clause's shape is a property of one
/// DECOMPOSITION, not of the set it denotes, so it would split a group that
/// equivalence does not.
///
/// Inhabited-ness is read straight off the clauses because normalization cannot
/// change it: saturation and widening keep an axis non-empty, and the
/// subsumption drop always leaves a survivor (the last clause standing has
/// nothing left to be covered by).
fn descr_fingerprint(cx: TyCtx<'_>, d: &Descr) -> String {
    if d.is_empty_memo(cx, &mut Memo::default()) {
        return "fp[none]".to_string();
    }
    if is_full(cx, d) {
        return "fp[any]".to_string();
    }
    let mut parts = basic_names(d.basic);
    push_key(&mut parts, "a", &d.atoms, |name| format!(":{name}"));
    push_key(&mut parts, "o", &d.opaques, Clone::clone);
    if !d.brands.is_any() {
        push_key(&mut parts, "n", &d.brands, Clone::clone);
    }
    push_key(&mut parts, "v", &d.vars, |id| cx.render_var(*id));
    let structural: String = [
        (inhabited(cx, &d.tuples, emptiness::tuple_clause_empty), "T"),
        (inhabited(cx, &d.lists, emptiness::list_clause_empty), "L"),
        (inhabited(cx, &d.resources, emptiness::resource_clause_empty), "R"),
        (inhabited(cx, &d.funcs, emptiness::func_clause_empty), "F"),
        (inhabited(cx, &d.maps, emptiness::map_clause_empty), "M"),
    ]
    .iter()
    .filter(|(present, _)| *present)
    .map(|(_, letter)| *letter)
    .collect();
    if !structural.is_empty() {
        parts.push(structural);
    }
    format!("fp[{}]", parts.join(";"))
}

fn inhabited<T>(cx: TyCtx<'_>, clauses: &[Conj<T>], is_empty: fn(TyCtx<'_>, &Conj<T>, &mut Memo) -> bool) -> bool {
    clauses.iter().any(|c| !is_empty(cx, c, &mut Memo::default()))
}

/// A descriptor is FULL when it contains `any`. `looks_full` proves it
/// structurally; the semantic check behind it is reached only for a descriptor
/// that already meets every necessary condition (every scalar axis saturated
/// and every structural axis inhabited), which keeps the negation it costs off
/// the common path.
fn is_full(cx: TyCtx<'_>, d: &Descr) -> bool {
    if d.looks_full() {
        return true;
    }
    let saturated = d.basic == BasicBits::ALL
        && d.atoms.is_any()
        && d.opaques.is_any()
        && d.brands.is_any()
        && d.vars.is_any()
        && !d.tuples.is_empty()
        && !d.lists.is_empty()
        && !d.resources.is_empty()
        && !d.funcs.is_empty()
        && !d.maps.is_empty();
    saturated && Descr::any().is_subtype(cx, d)
}

fn sorted(texts: impl Iterator<Item = String>) -> Vec<String> {
    let mut out: Vec<String> = texts.collect();
    out.sort();
    out
}

fn basic_names(basic: BasicBits) -> Vec<String> {
    BASIC_NAMES
        .iter()
        .filter(|(bit, _)| basic.contains_all(*bit))
        .map(|(_, name)| (*name).to_string())
        .collect()
}

fn push_set<T, F>(parts: &mut Vec<String>, set: &FiniteSet<T>, top: &str, render: F)
where
    T: Ord + Clone,
    F: Fn(&T) -> String,
{
    if set.is_none() {
        return;
    }
    if set.is_any() {
        parts.push(top.to_string());
        return;
    }
    let rendered = sorted(set.values.iter().map(render));
    if set.cofinite {
        parts.push(format!("not({})", rendered.join(" | ")));
    } else {
        parts.push(rendered.join(" | "));
    }
}

/// One nominal axis's contribution to the fingerprint, omitted entirely when
/// the axis is empty so the prefix stays short enough to sit in front of every
/// rendered type.
fn push_key<T, F>(parts: &mut Vec<String>, tag: &str, set: &FiniteSet<T>, render: F)
where
    T: Ord + Clone,
    F: Fn(&T) -> String,
{
    if set.is_none() {
        return;
    }
    let rendered = sorted(set.values.iter().map(render));
    parts.push(format!(
        "{tag}{}{}",
        if set.cofinite { "!" } else { "" },
        rendered.join("+")
    ));
}

fn map_key(key: &MapKey) -> String {
    match key {
        MapKey::Atom(name) => format!(":{name}"),
        MapKey::Int(value) => value.to_string(),
    }
}
