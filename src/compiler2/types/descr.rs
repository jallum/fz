//! Private descriptor for the interned type implementation.

use super::bits::BasicBits;
use super::conj::Conj;
use super::dnf::{dnf_intersect, dnf_neg, dnf_union, is_dnf_top, normalize_empty_nonempty_list_unions};
use super::emptiness::{
    Memo, func_clause_empty, list_clause_empty, map_clause_empty, resource_clause_empty, tuple_clause_empty,
};
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, ResourceSig, TupleSig};
use super::{MapKey, Ty, TyCtx, TypeVarId};
use crate::finite_set::FiniteSet;

/// Singleton-type precision for atoms (and the atom-shaped nominal axes:
/// opaques, brands, vars — see [`VarSet`]). Numbers deliberately have no
/// literal sets — numeric constants are values, not types.
type AtomSet = FiniteSet<String>;

/// Parametric type-variable identifier. Vars are nominal placeholders
/// distinguished only by id; the lattice cannot tell them apart from opaques.
/// The difference is at use sites: opaques are fixed (the name *is* the type);
/// vars are substituted at instantiation sites.
///
/// Per-function scoping is handled by the planner, which renames at
/// function-typing entry to ensure alpha-equivalence across signatures; the id
/// itself carries no scope.
type VarSet = FiniteSet<TypeVarId>;

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(super) struct Descr {
    pub(super) basic: BasicBits,
    pub(super) atoms: AtomSet,
    pub(super) opaques: FiniteSet<String>,
    pub(super) brands: FiniteSet<String>,
    pub(super) vars: VarSet,
    pub(super) tuples: Vec<Conj<TupleSig>>,
    pub(super) lists: Vec<Conj<ListSig>>,
    pub(super) resources: Vec<Conj<ResourceSig>>,
    pub(super) funcs: Vec<Conj<ArrowSig>>,
    pub(super) maps: Vec<Conj<MapSig>>,
}

impl Descr {
    pub(super) fn any() -> Self {
        Self {
            basic: BasicBits::ALL,
            atoms: AtomSet::any(),
            opaques: FiniteSet::any(),
            brands: FiniteSet::any(),
            vars: VarSet::any(),
            tuples: vec![Conj::top()],
            lists: vec![Conj::top()],
            resources: vec![Conj::top()],
            funcs: vec![Conj::top()],
            maps: vec![Conj::top()],
        }
    }

    /// The builder base for a VALUE constructor: no structural content yet,
    /// and the brand slot unconstrained. `brands` is a conjunctive REFINEMENT
    /// factor, not a kind of value — an unbranded `int` admits a branded int
    /// (`Meters <: int`), so its slot is top, and `Descr::none()`'s bottom slot
    /// is what makes `none` the union identity on that axis.
    pub(super) fn unbranded() -> Self {
        Self {
            brands: FiniteSet::any(),
            ..Self::none()
        }
    }

    pub(super) fn none() -> Self {
        Self {
            basic: BasicBits::NONE,
            atoms: AtomSet::none(),
            opaques: FiniteSet::none(),
            brands: FiniteSet::none(),
            vars: VarSet::none(),
            tuples: Vec::new(),
            lists: Vec::new(),
            resources: Vec::new(),
            funcs: Vec::new(),
            maps: Vec::new(),
        }
    }

    pub(super) fn opaque_of(name: impl Into<String>) -> Self {
        let mut d = Self::unbranded();
        d.opaques = FiniteSet::lit(name.into());
        d
    }

    pub(super) fn var(id: TypeVarId) -> Self {
        let mut d = Self::unbranded();
        d.vars = VarSet::lit(id);
        d
    }

    pub(super) fn nil() -> Self {
        Self::atom_lit("nil")
    }

    pub(super) fn bool_t() -> Self {
        let mut d = Self::unbranded();
        d.atoms = AtomSet::lit("true".to_string()).union(&AtomSet::lit("false".to_string()));
        d
    }

    pub(super) fn atom_top() -> Self {
        let mut d = Self::unbranded();
        d.atoms = AtomSet::any();
        d
    }

    /// The top of the function axis — "any callable", with no other axis. The
    /// canonical value-lane representative for every callable value: a callable's
    /// runtime layout is one word (a code pointer or a closure ref) regardless of
    /// signature or identity, so every callable shares this one lane.
    pub(super) fn fun_top() -> Self {
        let mut d = Self::unbranded();
        d.funcs = vec![Conj::top()];
        d
    }

    pub(super) fn atom_lit(name: impl Into<String>) -> Self {
        let mut d = Self::unbranded();
        d.atoms = AtomSet::lit(name.into());
        d
    }

    pub(super) fn int() -> Self {
        Self::from_basic(BasicBits::INT)
    }

    pub(super) fn float() -> Self {
        Self::from_basic(BasicBits::FLOAT)
    }

    pub(super) fn str_t() -> Self {
        Self::from_basic(BasicBits::BINARY)
    }

    fn from_basic(basic: BasicBits) -> Self {
        let mut d = Self::unbranded();
        d.basic = basic;
        d
    }

    pub(super) fn resource_of(cx: TyCtx<'_>, payload: Ty) -> Self {
        if cx.descr(&payload).is_empty(cx) {
            return Self::none();
        }
        let mut d = Self::unbranded();
        d.resources = vec![Conj::pos_of(ResourceSig { payload })];
        d
    }

    pub(super) fn tuple_of(elems: impl IntoIterator<Item = Ty>) -> Self {
        let mut d = Self::unbranded();
        d.tuples.push(Conj::pos_of(TupleSig {
            elems: elems.into_iter().collect(),
        }));
        d
    }

    pub(super) fn list_sig(sig: ListSig) -> Self {
        let mut d = Self::unbranded();
        d.lists.push(Conj::pos_of(sig));
        d
    }

    pub(super) fn list_of(cx: TyCtx<'_>, elem: Ty) -> Self {
        Self::list_sig(ListSig::possibly_empty(&cx, elem))
    }

    pub(super) fn non_empty_list_of(cx: TyCtx<'_>, elem: Ty) -> Self {
        ListSig::non_empty(&cx, elem)
            .map(Self::list_sig)
            .unwrap_or_else(Self::none)
    }

    pub(super) fn empty_list() -> Self {
        Self::list_sig(ListSig::empty())
    }

    pub(super) fn arrow(args: impl IntoIterator<Item = Ty>, ret: Ty) -> Self {
        let mut d = Self::unbranded();
        d.funcs.push(Conj::pos_of(ArrowSig {
            args: args.into_iter().collect(),
            ret,
            lit: None,
        }));
        d
    }

    pub(super) fn map_top() -> Self {
        let mut d = Self::unbranded();
        d.maps.push(Conj::top());
        d
    }

    pub(super) fn map_of(fields: impl IntoIterator<Item = (MapKey, Ty)>) -> Self {
        let mut d = Self::unbranded();
        d.maps.push(Conj::pos_of(MapSig {
            fields: fields.into_iter().collect(),
        }));
        d
    }

    pub(super) fn as_atom_singleton(&self) -> Option<&str> {
        (!self.atoms.cofinite && self.atoms.values.len() == 1)
            .then(|| self.atoms.values.iter().next().map(String::as_str))
            .flatten()
    }

    pub(super) fn atom_literals(&self) -> Option<Vec<String>> {
        (!self.atoms.cofinite).then(|| self.atoms.values.iter().cloned().collect())
    }

    pub(super) fn as_opaque_singleton(&self) -> Option<&str> {
        (!self.opaques.cofinite && self.opaques.values.len() == 1)
            .then(|| self.opaques.values.iter().next().map(String::as_str))
            .flatten()
    }

    #[cfg(test)]
    pub(super) fn as_brand_singleton(&self) -> Option<&str> {
        (!self.brands.cofinite && self.brands.values.len() == 1)
            .then(|| self.brands.values.iter().next().map(String::as_str))
            .flatten()
    }

    #[cfg(test)]
    pub(super) fn as_tuple_singleton(&self) -> Option<&[Ty]> {
        if self.basic.is_empty()
            && self.atoms.is_none()
            && self.opaques.is_none()
            && self.brands.is_any()
            && self.vars.is_none()
            && self.lists.is_empty()
            && self.resources.is_empty()
            && self.funcs.is_empty()
            && self.maps.is_empty()
            && self.tuples.len() == 1
            && self.tuples[0].neg.is_empty()
            && self.tuples[0].pos.len() == 1
        {
            Some(&self.tuples[0].pos[0].elems)
        } else {
            None
        }
    }

    pub(super) fn as_closure_lit(&self) -> Option<&ClosureLit> {
        (self.funcs.len() == 1 && self.funcs[0].neg.is_empty() && self.funcs[0].pos.len() == 1)
            .then(|| self.funcs[0].pos[0].lit.as_ref())
            .flatten()
    }

    pub(super) fn is_singleton_literal(&self) -> bool {
        // Only atoms have singleton types; numeric constants are values.
        self.as_atom_singleton().is_some()
    }

    pub(super) fn max_tuple_arity(&self) -> usize {
        self.tuples
            .iter()
            .flat_map(|c| c.pos.iter().map(|sig| sig.elems.len()))
            .max()
            .unwrap_or(0)
    }

    pub(super) fn refine_map_field(&self, key: &MapKey, vt: Ty) -> Descr {
        let mut out = self.clone();
        for clause in &mut out.maps {
            for sig in &mut clause.pos {
                sig.fields.insert(key.clone(), vt);
            }
        }
        out
    }

    pub(super) fn as_pure_list(&self, _cx: TyCtx<'_>) -> Option<&ListSig> {
        self.axis_free()
            .then_some(())
            .and_then(|_| single_positive(&self.lists))
            .filter(|_| {
                self.tuples.is_empty() && self.resources.is_empty() && self.funcs.is_empty() && self.maps.is_empty()
            })
    }

    /// True when this type is purely the list FAMILY — one or more list
    /// alternatives (e.g. `[int] | []`) and nothing on any other axis. Unlike
    /// [`as_pure_list`](Self::as_pure_list) it admits a union of list shapes, so
    /// the addressed convergence class can collapse a recursive list-family slot
    /// (`[int] | []`) to one addressed-element list rather than leaving the union
    /// uncollapsed (fz-f98.14.10.2).
    pub(super) fn is_pure_list_family(&self) -> bool {
        self.axis_free()
            && !self.lists.is_empty()
            && self.tuples.is_empty()
            && self.resources.is_empty()
            && self.funcs.is_empty()
            && self.maps.is_empty()
    }

    pub(super) fn projection_alternatives(&self) -> Option<Vec<Descr>> {
        if !self.axis_free() {
            return None;
        }
        let populated_axes = [
            !self.tuples.is_empty(),
            !self.lists.is_empty(),
            !self.resources.is_empty(),
            !self.funcs.is_empty(),
            !self.maps.is_empty(),
        ]
        .into_iter()
        .filter(|populated| *populated)
        .count();
        if populated_axes != 1 {
            return None;
        }
        if self.tuples.len() > 1 {
            return Some(
                self.tuples
                    .iter()
                    .cloned()
                    .map(|clause| {
                        let mut alternative = Descr::unbranded();
                        alternative.tuples.push(clause);
                        alternative
                    })
                    .collect(),
            );
        }
        if self.lists.len() > 1 {
            return Some(
                self.lists
                    .iter()
                    .cloned()
                    .map(|clause| {
                        let mut alternative = Descr::unbranded();
                        alternative.lists.push(clause);
                        alternative
                    })
                    .collect(),
            );
        }
        None
    }

    pub(super) fn pure_tuple(&self) -> Option<&TupleSig> {
        self.axis_free()
            .then_some(())
            .and_then(|_| single_positive(&self.tuples))
            .filter(|_| {
                self.lists.is_empty() && self.resources.is_empty() && self.funcs.is_empty() && self.maps.is_empty()
            })
    }

    pub(super) fn pure_resource(&self) -> Option<&ResourceSig> {
        self.axis_free()
            .then_some(())
            .and_then(|_| single_positive(&self.resources))
            .filter(|_| {
                self.tuples.is_empty() && self.lists.is_empty() && self.funcs.is_empty() && self.maps.is_empty()
            })
    }

    pub(super) fn pure_arrow(&self) -> Option<&ArrowSig> {
        self.axis_free()
            .then_some(())
            .and_then(|_| single_positive(&self.funcs))
            .filter(|_| {
                self.tuples.is_empty() && self.lists.is_empty() && self.resources.is_empty() && self.maps.is_empty()
            })
    }

    /// True when this type is purely a callable — one or more function clauses
    /// and nothing on any other axis. Unlike [`pure_arrow`] it admits a UNION of
    /// clauses (an opaque join of functions). `any` is excluded: it is not
    /// `axis_free`. This is the layout test for "this value is a callable word"
    /// driving the value-lane collapse.
    pub(super) fn is_pure_callable(&self) -> bool {
        self.axis_free()
            && !self.funcs.is_empty()
            && self.tuples.is_empty()
            && self.lists.is_empty()
            && self.resources.is_empty()
            && self.maps.is_empty()
    }

    pub(super) fn pure_map(&self) -> Option<&MapSig> {
        self.axis_free()
            .then_some(())
            .and_then(|_| single_positive(&self.maps))
            .filter(|_| {
                self.tuples.is_empty() && self.lists.is_empty() && self.resources.is_empty() && self.funcs.is_empty()
            })
    }

    fn axis_free(&self) -> bool {
        self.basic.is_empty()
            && self.atoms.is_none()
            && self.opaques.is_none()
            && self.brands.is_any()
            && self.vars.is_none()
    }

    /// The structural union carries nothing — the descriptor denotes the empty
    /// set however its brand slot reads.
    fn structure_looks_empty(&self) -> bool {
        self.basic.is_empty()
            && self.atoms.is_none()
            && self.opaques.is_none()
            && self.vars.is_none()
            && self.tuples.is_empty()
            && self.lists.is_empty()
            && self.resources.is_empty()
            && self.funcs.is_empty()
            && self.maps.is_empty()
    }

    /// A refinement of nothing is nothing, and a value carries at most one
    /// brand, so an empty brand slot (`Meters and Feet`) is empty too.
    pub(super) fn looks_empty(&self) -> bool {
        self.brands.is_none() || self.structure_looks_empty()
    }

    pub(super) fn looks_full(&self) -> bool {
        self.basic == BasicBits::ALL
            && self.atoms.is_any()
            && self.opaques.is_any()
            && self.brands.is_any()
            && self.vars.is_any()
            && is_dnf_top(&self.tuples)
            && is_dnf_top(&self.lists)
            && is_dnf_top(&self.resources)
            && is_dnf_top(&self.funcs)
            && is_dnf_top(&self.maps)
    }

    /// The brand slot joins pointwise, which is exact whenever the operands
    /// agree on one factor (`Meters | int = int`, `Meters | Feet` = the two
    /// brands over one inner) and a hull when they differ on both
    /// (`Meters | utf8` widens to "int or binary, any brand").
    ///
    /// A BOTTOM is the identity first, before any of that. Bottom no longer
    /// has one shape — a structural meet (`int and binary`) empties the kind
    /// axes and leaves the slot at top, a brand meet (`Meters and Feet`)
    /// empties the slot and leaves the kind axes inhabited — so a pointwise
    /// hull would read an EMPTY operand's factors as constraints and widen the
    /// other side by them: `nothing | Meters(int)` would answer `int`.
    /// [`looks_empty`](Self::looks_empty) is the one bottom test, and asking
    /// it here is what keeps `∅ ∪ x = x` a law rather than a property of one
    /// interned identity.
    pub(super) fn union(&self, _cx: TyCtx<'_>, other: &Descr) -> Descr {
        if self.looks_empty() {
            // A join of two nothings is THE nothing: answering with either
            // operand would make the join non-commutative in the interned id
            // it produces, for no gain.
            return if other.looks_empty() {
                Descr::none()
            } else {
                other.clone()
            };
        }
        if other.looks_empty() {
            return self.clone();
        }
        Descr {
            basic: self.basic.union(other.basic),
            atoms: self.atoms.union(&other.atoms),
            opaques: self.opaques.union(&other.opaques),
            brands: self.brands.union(&other.brands),
            vars: self.vars.union(&other.vars),
            tuples: dnf_union(&self.tuples, &other.tuples),
            lists: normalize_empty_nonempty_list_unions(dnf_union(&self.lists, &other.lists)),
            resources: dnf_union(&self.resources, &other.resources),
            funcs: dnf_union(&self.funcs, &other.funcs),
            maps: dnf_union(&self.maps, &other.maps),
        }
    }

    /// Exact on every axis: a rectangle meets a rectangle. Two brands over one
    /// inner meet at an EMPTY slot, which is what makes `Meters and Feet`
    /// empty — a value carries at most one brand.
    pub(super) fn intersect(&self, other: &Descr) -> Descr {
        Descr {
            basic: self.basic.intersect(other.basic),
            atoms: self.atoms.intersect(&other.atoms),
            opaques: self.opaques.intersect(&other.opaques),
            brands: self.brands.intersect(&other.brands),
            vars: self.vars.intersect(&other.vars),
            tuples: dnf_intersect(&self.tuples, &other.tuples),
            lists: dnf_intersect(&self.lists, &other.lists),
            resources: dnf_intersect(&self.resources, &other.resources),
            funcs: dnf_intersect(&self.funcs, &other.funcs),
            maps: dnf_intersect(&self.maps, &other.maps),
        }
    }

    /// The complement of the STRUCTURAL union alone, with the brand slot left
    /// unconstrained — the factor [`diff`](Self::diff) subtracts on its own.
    ///
    /// There is deliberately no whole-descriptor `neg`: the complement of a
    /// refinement is `¬structure` OR `structure with another brand`, two
    /// rectangles this representation cannot hold at once, so it could only
    /// widen to `any` — a "negation" that forgets the brand entirely. `diff`
    /// subtracts the two factors separately instead and stays exact, so
    /// difference, not complement, is the primitive callers get.
    fn neg_structure(&self) -> Descr {
        Descr {
            brands: FiniteSet::any(),
            basic: self.basic.neg(),
            atoms: self.atoms.neg(),
            opaques: self.opaques.neg(),
            vars: self.vars.neg(),
            tuples: dnf_neg(&self.tuples),
            lists: dnf_neg(&self.lists),
            resources: dnf_neg(&self.resources),
            funcs: dnf_neg(&self.funcs),
            maps: dnf_neg(&self.maps),
        }
    }

    /// `(S, B) \ (S', B') = (S \ S', B) union (S and S', B \ B')` — a union of
    /// two rectangles, of which this representation holds one. Three cases
    /// collapse it to one and are EXACT, and they are the cases a brand model
    /// actually produces:
    ///
    /// - the subtrahend's slot covers ours: the second rectangle is empty, so
    ///   the structural subtraction alone answers. `Meters \ int` is empty (a
    ///   brand is inside its inner);
    /// - the slots are disjoint: the subtrahend removes nothing, so `Meters \
    ///   Feet` is `Meters`;
    /// - the structures are equal — a brand beside its own inner, which is how
    ///   `mint_brand` builds one: the first rectangle is empty, so the slot
    ///   subtraction alone answers. `int \ Meters` is "an int not branded
    ///   Meters", which keeps `int` inhabited without swallowing `Meters`.
    ///
    /// What is left over-approximates: partial slot overlap across DIFFERENT
    /// structures (`(Meters | utf8) \ Meters`) is two rectangles that no
    /// single descriptor holds, so the whole minuend is returned. Every
    /// consumer asks `diff(..).is_empty()`, where a too-big difference can only
    /// answer `is_subtype = false`.
    pub(super) fn diff(&self, other: &Descr) -> Descr {
        if other.brands.contains_all(&self.brands) {
            let mut d = self.intersect(&other.neg_structure());
            d.brands = self.brands.clone();
            return d;
        }
        if !self.brands.overlaps(&other.brands) {
            return self.clone();
        }
        if self.same_structure_by_construction(other) {
            let mut d = self.clone();
            d.brands = self.brands.intersect(&other.brands.neg());
            return d;
        }
        self.clone()
    }

    /// SYNTACTICALLY equal on every kind axis — the two descriptors differ, if
    /// at all, only in their brand slot. It is exact where it matters BY
    /// CONSTRUCTION: `mint_brand` builds a refinement by cloning its inner's
    /// structure, so a brand and its inner are literally equal here. It stays
    /// syntactic on purpose — asking whether the two structures are
    /// EQUIVALENT would call `is_equiv` -> `is_subtype` -> `diff` -> here, a
    /// recursion the emptiness `Memo` does not guard. Interned children
    /// compare by id, so two ids denoting one type answer `false` and cost
    /// precision, never soundness.
    fn same_structure_by_construction(&self, other: &Descr) -> bool {
        self.basic == other.basic
            && self.atoms == other.atoms
            && self.opaques == other.opaques
            && self.vars == other.vars
            && self.tuples == other.tuples
            && self.lists == other.lists
            && self.resources == other.resources
            && self.funcs == other.funcs
            && self.maps == other.maps
    }

    pub(super) fn is_empty(&self, cx: TyCtx<'_>) -> bool {
        let mut memo = Memo::default();
        self.is_empty_memo(cx, &mut memo)
    }

    pub(super) fn is_empty_memo(&self, cx: TyCtx<'_>, memo: &mut Memo) -> bool {
        if memo.in_flight.contains(self) {
            return true;
        }
        memo.in_flight.insert(self.clone());
        let result = self.brands.is_none()
            || self.basic.is_empty()
                && self.atoms.is_none()
                && self.opaques.is_none()
                && self.vars.is_none()
                && self.tuples.iter().all(|c| tuple_clause_empty(cx, c, memo))
                && self.lists.iter().all(|c| list_clause_empty(cx, c, memo))
                && self.resources.iter().all(|c| resource_clause_empty(cx, c, memo))
                && self.funcs.iter().all(|c| func_clause_empty(cx, c, memo))
                && self.maps.iter().all(|c| map_clause_empty(cx, c, memo));
        memo.in_flight.remove(self);
        result
    }

    pub(super) fn is_subtype(&self, cx: TyCtx<'_>, other: &Descr) -> bool {
        self.diff(other).is_empty(cx)
    }

    pub(super) fn is_equiv(&self, cx: TyCtx<'_>, other: &Descr) -> bool {
        self == other || (self.is_subtype(cx, other) && other.is_subtype(cx, self))
    }

    pub(super) fn value_disjoint(&self, cx: TyCtx<'_>, other: &Descr) -> bool {
        self.erase_nominal(cx).intersect(&other.erase_nominal(cx)).is_empty(cx)
    }

    fn erase_nominal(&self, cx: TyCtx<'_>) -> Descr {
        // Erasure drops a REFINEMENT, so it can only ever keep or widen the
        // set — except at the bottom whose emptiness IS the empty slot
        // (`Meters and Feet`), where releasing the slot would resurrect the
        // inner as a live `int` and tell the brand-blind runtime question
        // (`is_value_disjoint`) that an uninhabited type shares values.
        if self.looks_empty() {
            return Descr::none();
        }
        let mut d = self.clone();
        // A brand refines the structure held in this same descriptor, so
        // dropping the refinement — releasing the slot to top — is the whole
        // erasure: the inner is already the structural axes, whatever the slot
        // said. `utf8` erases to `binary`, and `binary` erases to itself.
        d.brands = FiniteSet::any();
        let opaques = std::mem::replace(&mut d.opaques, FiniteSet::none());
        // Opaques carry no embedded inner (opaque_of sets only the tag axis); erase conservatively.
        if !opaques.is_none() {
            d = d.union(cx, &Descr::any());
        }
        d
    }
}

fn single_positive<T>(clauses: &[Conj<T>]) -> Option<&T> {
    let [clause] = clauses else {
        return None;
    };
    if !clause.neg.is_empty() {
        return None;
    }
    let [sig] = clause.pos.as_slice() else {
        return None;
    };
    Some(sig)
}
