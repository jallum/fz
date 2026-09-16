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
//! possibly-empty and the non-empty list identically as `[T]`, and it renders a
//! clause from the factors it was built out of rather than from what it
//! denotes. A false equivalence is far worse than a false difference for an
//! equivalence oracle, so this rendering distinguishes every form the lattice
//! does. Both surfaces DO name the five axis tops apart from `any`: this one as
//! `tuple`/`list`/`fun`/`map`/`resource`, `display` as the widest type a user
//! could write where there is one (`[any]`, `resource(any)`).
//!
//! Normalization runs on DESCRIPTORS, not only on interned `Ty`s: a list
//! clause's intersected element fragment is a descriptor that was never
//! interned, and interning it here would mutate the very arena the canon
//! describes.

use std::collections::HashMap;
use std::sync::Arc;

use crate::finite_set::FiniteSet;
use crate::fz_ir::FnId;

use super::axis;
use super::bits::{BASIC_NAMES, BasicBits};
use super::conj::Conj;
use super::descr::Descr;
use super::emptiness::{self, Memo, NonEmptyLists};
use super::format::brand_refinement;
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, MapTag, ResourceSig, TupleSig};
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
    #[cfg(test)]
    alpha_names: Option<HashMap<TypeVarId, usize>>,
    #[cfg(test)]
    structural_alpha_names: HashMap<TypeVarId, String>,
}

impl<'a> TyCanon<'a> {
    pub(crate) fn new(labels: &'a dyn Fn(FnId) -> String) -> Self {
        Self {
            labels,
            bodies: HashMap::new(),
            fingerprints: HashMap::new(),
            whole: HashMap::new(),
            #[cfg(test)]
            alpha_names: None,
            #[cfg(test)]
            structural_alpha_names: HashMap::new(),
        }
    }

    #[cfg(test)]
    pub(crate) fn alpha_normalized(labels: &'a dyn Fn(FnId) -> String) -> Self {
        let mut canon = Self::new(labels);
        canon.alpha_names = Some(HashMap::new());
        canon
    }

    #[cfg(test)]
    pub(crate) fn name_structural_alpha(&mut self, id: TypeVarId, name: String) {
        self.structural_alpha_names.insert(id, name);
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
    pub(crate) fn var(&mut self, types: &Types, id: TypeVarId) -> String {
        self.var_text(types.ctx(), id)
    }

    fn var_text(&mut self, cx: TyCtx<'_>, id: TypeVarId) -> String {
        let raw = cx.render_var(id);
        #[cfg(test)]
        if let Some(name) = self.structural_alpha_names.get(&id) {
            return name.clone();
        }
        #[cfg(test)]
        if raw.starts_with('α')
            && let Some(names) = &mut self.alpha_names
        {
            let next = names.len();
            return format!("free{}", *names.entry(id).or_insert(next));
        }
        raw
    }

    fn fingerprint_at(&mut self, cx: TyCtx<'_>, ty: Ty) -> Arc<str> {
        if let Some(hit) = self.fingerprints.get(&ty) {
            return Arc::clone(hit);
        }
        let text: Arc<str> = descr_fingerprint(cx, cx.descr(&ty), |id| self.var_text(cx, id)).into();
        self.fingerprints.insert(ty, Arc::clone(&text));
        text
    }

    fn body(&mut self, cx: TyCtx<'_>, ty: Ty) -> Arc<str> {
        if let Some(hit) = self.bodies.get(&ty) {
            return Arc::clone(hit);
        }
        let text: Arc<str> = self.descr_body(cx, cx.descr(&ty), Provenance::Interned).into();
        self.bodies.insert(ty, Arc::clone(&text));
        text
    }

    // ------------------------------------------------------------------
    // Body
    // ------------------------------------------------------------------

    /// The empty-clause drop and the axis absorption below are the boundary's
    /// own rules, so a descriptor that came from the INTERNER already
    /// satisfies both and neither is repeated on one. A descriptor this module
    /// built itself — a list clause's intersected element fragment — never
    /// reached the interner, so it gets them here, from the same functions.
    fn descr_body(&mut self, cx: TyCtx<'_>, d: &Descr, provenance: Provenance) -> String {
        if d.is_empty_memo(cx, &mut Memo::default()) {
            return "none".to_string();
        }
        if d.is_full(cx) {
            return "any".to_string();
        }
        let normalized;
        let d = match provenance {
            Provenance::Interned => d,
            Provenance::Synthesized => {
                let mut swept = d.clone();
                axis::drop_empty_clauses(cx, &mut swept, &|ty| cx.descr(ty).is_empty(cx));
                normalized = swept;
                &normalized
            }
        };
        let axes = self.axes(cx, d, provenance);
        let mut parts: Vec<String> = basic_names(d.basic);
        push_set(&mut parts, &d.atoms, "atom", |name| format!(":{name}"));
        push_set(&mut parts, &d.opaques, "opaque", ToString::to_string);
        push_set(&mut parts, &d.vars, "var", |id| self.var_text(cx, *id));
        parts.extend(sorted(
            self.clause_texts(cx, &axes.tuples, Self::tuple_clause).into_iter(),
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

    /// One clause rendered with its factors sorted. `top` names the clause with
    /// no factors (`Conj::top()`) — "every tuple", "every list", and so on —
    /// which `types::axis` makes the ONE spelling of an axis's top, so this is
    /// the form every saturated axis arrives in.
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
        factors.join(" & ")
    }

    fn tuple_clause(&mut self, cx: TyCtx<'_>, c: &Conj<TupleSig>) -> String {
        self.conj_text(cx, c, Self::tuple_sig, "tuple")
    }

    /// A list clause rendered from what it DENOTES, by the one reading of a
    /// list clause ([`emptiness::list_denotation`]).
    ///
    /// The reading is computed rather than read off the sig for two reasons.
    /// The descriptors this module builds ITSELF never reach the interner, and
    /// one of those rendered unnormalized would report two carvings of a type
    /// as two types. And `Types::intern` writes the reading back only for
    /// ground clauses and for var-bearing clauses that need no element
    /// arithmetic: a var-bearing clause that needs it is stored as it was
    /// built, so `non_empty_list(α) \ non_empty_list(int)` is a second id over
    /// the denotation `non_empty_list(α)` already has. Rendering the
    /// denotation here regardless gives that pair ONE canonical form, which is
    /// what lets the census count it as one denotation holding two ids instead
    /// of hiding it as a difference that is not there.
    fn list_clause(&mut self, cx: TyCtx<'_>, c: &Conj<ListSig>) -> String {
        if c.pos.is_empty() && c.neg.is_empty() {
            return "list".to_string();
        }
        let Some(denotation) = emptiness::list_denotation(cx, c, &mut Memo::default()) else {
            return "none".to_string();
        };
        let Some(NonEmptyLists { elem, minus }) = denotation.non_empty else {
            return "empty_list()".to_string();
        };
        let head = if denotation.holds_empty {
            "list"
        } else {
            "non_empty_list"
        };
        let mut factors = vec![format!(
            "{head}({})",
            self.descr_body(cx, &elem, Provenance::Synthesized)
        )];
        for cut in &minus {
            let rendered = self.descr_body(cx, cut, Provenance::Synthesized);
            factors.push(format!("not(non_empty_list({rendered}))"));
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
        match &sig.tag {
            MapTag::Plain => format!("%{{{}}}", fields.join(", ")),
            MapTag::Struct(tag) => format!("%{}{{{}}}", tag.name, fields.join(", ")),
        }
    }

    // ------------------------------------------------------------------
    // Normalization
    // ------------------------------------------------------------------

    /// The persistence boundary has already absorbed every stored axis it can
    /// normalize. Only a list fragment synthesized by this renderer needs the
    /// shared rules again: descriptor arithmetic concatenates clauses after
    /// their children were interned.
    fn axes(&mut self, cx: TyCtx<'_>, d: &Descr, provenance: Provenance) -> Axes {
        let subtype = &|narrower: &Ty, wider: &Ty| cx.descr(narrower).is_subtype(cx, cx.descr(wider));
        let covers = &|wider: &Descr, narrower: &Descr| narrower.is_subtype(cx, wider);
        let mut tuples = d.tuples.clone();
        let mut lists = d.lists.clone();
        let mut resources = d.resources.clone();
        let mut maps = d.maps.clone();
        if matches!(provenance, Provenance::Synthesized) {
            axis::merge_empty_list_clause(&mut lists);
            axis::absorb_axis(cx, &mut tuples, subtype, covers, &axis::TUPLES);
            axis::absorb_axis(cx, &mut lists, subtype, covers, &axis::LISTS);
            axis::absorb_axis(cx, &mut resources, subtype, covers, &axis::RESOURCES);
            axis::absorb_axis(cx, &mut maps, subtype, covers, &axis::MAPS);
        }

        Axes {
            tuples,
            lists,
            resources,
            funcs: d.funcs.clone(),
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

/// Where a descriptor came from. One that reached the interner is already in
/// the boundary's normal form; one this module built is not.
#[derive(Clone, Copy)]
enum Provenance {
    Interned,
    Synthesized,
}

/// The per-axis DNFs after normalization.
struct Axes {
    tuples: Vec<Conj<TupleSig>>,
    lists: Vec<Conj<ListSig>>,
    resources: Vec<Conj<ResourceSig>>,
    funcs: Vec<Conj<ArrowSig>>,
    maps: Vec<Conj<MapSig>>,
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
/// change it: saturation keeps an axis non-empty, and the subsumption drop
/// always leaves a survivor (the last clause standing has nothing left to be
/// covered by).
fn descr_fingerprint(cx: TyCtx<'_>, d: &Descr, mut render_var: impl FnMut(TypeVarId) -> String) -> String {
    if d.is_empty_memo(cx, &mut Memo::default()) {
        return "fp[none]".to_string();
    }
    if d.is_full(cx) {
        return "fp[any]".to_string();
    }
    let mut parts = basic_names(d.basic);
    push_key(&mut parts, "a", &d.atoms, |name| format!(":{name}"));
    push_key(&mut parts, "o", &d.opaques, ToString::to_string);
    if !d.brands.is_any() {
        push_key(&mut parts, "n", &d.brands, Clone::clone);
    }
    push_key(&mut parts, "v", &d.vars, |id| render_var(*id));
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
    F: FnMut(&T) -> String,
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
    F: FnMut(&T) -> String,
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
