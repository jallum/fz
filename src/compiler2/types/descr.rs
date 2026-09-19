//! Private descriptor for the interned type implementation.

use super::bits::BasicBits;
use super::conj::Conj;
use super::dnf::{dnf_intersect, dnf_neg, dnf_union, is_dnf_top};
use super::emptiness::{
    Memo, func_clause_empty, list_clause_empty, map_clause_empty, resource_clause_empty, tuple_clause_empty,
};
use super::sigs::{
    ArrowSig, ArrowSigOf, ClosureLit, ClosureLitOf, ListSig, ListSigOf, MapSig, MapSigOf, MapTag, ResourceSig,
    ResourceSigOf, StructTag, TupleSig, TupleSigOf,
};
use super::{BuiltinOpaque, MapKey, Ty, TyCtx, TypeVarId};
use crate::finite_set::FiniteSet;
use crate::modules::identity::ModuleName;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) enum OpaqueTag {
    Builtin(BuiltinOpaque),
    Named(String),
    ProtocolTarget(ModuleName),
}

impl std::fmt::Display for OpaqueTag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Builtin(builtin) => builtin.fmt(f),
            Self::Named(name) => f.write_str(name),
            Self::ProtocolTarget(module) => write!(f, "protocol-target({module})"),
        }
    }
}

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

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct DescrOf<R> {
    pub(super) basic: BasicBits,
    pub(super) atoms: AtomSet,
    pub(super) opaques: FiniteSet<OpaqueTag>,
    pub(super) brands: FiniteSet<String>,
    pub(super) vars: VarSet,
    pub(super) tuples: Vec<Conj<TupleSigOf<R>>>,
    pub(super) lists: Vec<Conj<ListSigOf<R>>>,
    pub(super) resources: Vec<Conj<ResourceSigOf<R>>>,
    pub(super) funcs: Vec<Conj<ArrowSigOf<R>>>,
    pub(super) maps: Vec<Conj<MapSigOf<R>>>,
}

pub(super) type Descr = DescrOf<Ty>;

pub(crate) fn union_of<R: Clone + PartialEq>(left: &DescrOf<R>, right: &DescrOf<R>) -> DescrOf<R> {
    if looks_empty(left) {
        return if looks_empty(right) {
            DescrOf::none()
        } else {
            right.clone()
        };
    }
    if looks_empty(right) {
        return left.clone();
    }
    DescrOf {
        basic: left.basic.union(right.basic),
        atoms: left.atoms.union(&right.atoms),
        opaques: left.opaques.union(&right.opaques),
        brands: left.brands.union(&right.brands),
        vars: left.vars.union(&right.vars),
        tuples: dnf_union(&left.tuples, &right.tuples),
        lists: dnf_union(&left.lists, &right.lists),
        resources: dnf_union(&left.resources, &right.resources),
        funcs: dnf_union(&left.funcs, &right.funcs),
        maps: dnf_union(&left.maps, &right.maps),
    }
}

fn looks_empty<R>(body: &DescrOf<R>) -> bool {
    body.brands.is_none()
        || (body.basic.is_empty()
            && body.atoms.is_none()
            && body.opaques.is_none()
            && body.vars.is_none()
            && body.tuples.is_empty()
            && body.lists.is_empty()
            && body.resources.is_empty()
            && body.funcs.is_empty()
            && body.maps.is_empty())
}

impl<R: Clone> DescrOf<R> {
    pub(crate) fn any() -> Self {
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
    pub(crate) fn unbranded() -> Self {
        Self {
            brands: FiniteSet::any(),
            ..Self::none()
        }
    }

    pub(crate) fn none() -> Self {
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

    pub(crate) fn opaque_of(name: impl Into<String>) -> Self {
        let mut d = Self::unbranded();
        d.opaques = FiniteSet::lit(OpaqueTag::Named(name.into()));
        d
    }

    pub(crate) fn builtin_opaque(builtin: BuiltinOpaque) -> Self {
        let mut d = Self::unbranded();
        d.opaques = FiniteSet::lit(OpaqueTag::Builtin(builtin));
        d
    }

    pub(super) fn struct_map(tag: StructTag, fields: BTreeMap<MapKey, R>) -> Self {
        let mut d = Self::unbranded();
        d.maps.push(Conj::pos_of(MapSigOf {
            tag: MapTag::Struct(tag),
            fields,
        }));
        d
    }

    pub(super) fn record(tag: MapTag, fields: impl IntoIterator<Item = (MapKey, R)>) -> Self {
        let mut d = Self::unbranded();
        d.maps.push(Conj::pos_of(MapSigOf {
            tag,
            fields: fields.into_iter().collect(),
        }));
        d
    }

    pub(crate) fn var(id: TypeVarId) -> Self {
        let mut d = Self::unbranded();
        d.vars = VarSet::lit(id);
        d
    }

    pub(crate) fn nil() -> Self {
        Self::atom_lit("nil")
    }

    pub(crate) fn bool_t() -> Self {
        let mut d = Self::unbranded();
        d.atoms = AtomSet::lit("true".to_string()).union(&AtomSet::lit("false".to_string()));
        d
    }

    pub(crate) fn atom_top() -> Self {
        let mut d = Self::unbranded();
        d.atoms = AtomSet::any();
        d
    }

    /// The top of the function axis — "any callable", with no other axis. The
    /// canonical value-lane representative for every callable value: a callable's
    /// runtime layout is one word (a code pointer or a closure ref) regardless of
    /// signature or identity, so every callable shares this one lane.
    pub(crate) fn fun_top() -> Self {
        let mut d = Self::unbranded();
        d.funcs = vec![Conj::top()];
        d
    }

    pub(crate) fn atom_lit(name: impl Into<String>) -> Self {
        let mut d = Self::unbranded();
        d.atoms = AtomSet::lit(name.into());
        d
    }

    pub(crate) fn int() -> Self {
        Self::from_basic(BasicBits::INT)
    }

    pub(crate) fn float() -> Self {
        Self::from_basic(BasicBits::FLOAT)
    }

    pub(crate) fn str_t() -> Self {
        Self::from_basic(BasicBits::BINARY)
    }

    fn from_basic(basic: BasicBits) -> Self {
        let mut d = Self::unbranded();
        d.basic = basic;
        d
    }

    pub(crate) fn resource_of(payload: R) -> Self {
        let mut d = Self::unbranded();
        d.resources = vec![Conj::pos_of(ResourceSigOf { payload })];
        d
    }

    pub(crate) fn tuple_of(elems: Vec<R>) -> Self {
        let mut d = Self::unbranded();
        d.tuples.push(Conj::pos_of(TupleSigOf { elems }));
        d
    }

    pub(crate) fn list_sig(sig: ListSigOf<R>) -> Self {
        let mut d = Self::unbranded();
        d.lists.push(Conj::pos_of(sig));
        d
    }

    pub(crate) fn list_of(elem: R) -> Self {
        Self::list_sig(ListSigOf::possibly_empty(elem))
    }

    pub(crate) fn non_empty_list_of(elem: R) -> Self {
        Self::list_sig(ListSigOf::non_empty(elem))
    }

    pub(crate) fn empty_list() -> Self {
        Self::list_sig(ListSigOf::empty())
    }

    pub(crate) fn arrow(args: impl IntoIterator<Item = R>, ret: R) -> Self {
        let mut d = Self::unbranded();
        d.funcs.push(Conj::pos_of(ArrowSigOf {
            args: args.into_iter().collect(),
            ret,
            lit: None,
        }));
        d
    }

    pub(crate) fn map_top() -> Self {
        Self::record(MapTag::Plain, [])
    }

    pub(crate) fn map_of(fields: BTreeMap<MapKey, R>) -> Self {
        let mut d = Self::unbranded();
        d.maps.push(Conj::pos_of(MapSigOf {
            tag: MapTag::Plain,
            fields,
        }));
        d
    }

    /// Rebuild this descriptor over another child-reference domain. Every
    /// structural child lives here, including closure captures, so a caller
    /// cannot accidentally transform an arrow surface but leave its
    /// environment in another reference world.
    pub(crate) fn map_children<S: Clone>(self, mut map: impl FnMut(R) -> S) -> DescrOf<S> {
        DescrOf {
            basic: self.basic,
            atoms: self.atoms,
            opaques: self.opaques,
            brands: self.brands,
            vars: self.vars,
            tuples: map_clauses(self.tuples, |sig| TupleSigOf {
                elems: sig.elems.into_iter().map(&mut map).collect(),
            }),
            lists: map_clauses(self.lists, |sig| ListSigOf {
                empty: sig.empty,
                elem: sig.elem.map(&mut map),
            }),
            resources: map_clauses(self.resources, |sig| ResourceSigOf {
                payload: map(sig.payload),
            }),
            funcs: map_clauses(self.funcs, |sig| ArrowSigOf {
                args: sig.args.into_iter().map(&mut map).collect(),
                ret: map(sig.ret),
                lit: sig.lit.map(|lit| ClosureLitOf {
                    kind: lit.kind,
                    fn_id: lit.fn_id,
                    captures: lit.captures.into_iter().map(&mut map).collect(),
                }),
            }),
            maps: map_clauses(self.maps, |sig| MapSigOf {
                tag: sig.tag,
                fields: sig.fields.into_iter().map(|(key, value)| (key, map(value))).collect(),
            }),
        }
    }
}

fn map_clauses<T, U>(clauses: Vec<Conj<T>>, mut map: impl FnMut(T) -> U) -> Vec<Conj<U>> {
    clauses
        .into_iter()
        .map(|clause| Conj {
            pos: clause.pos.into_iter().map(&mut map).collect(),
            neg: clause.neg.into_iter().map(&mut map).collect(),
        })
        .collect()
}

impl DescrOf<Ty> {
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
            .then(|| {
                self.opaques.values.iter().next().and_then(|tag| match tag {
                    OpaqueTag::Named(name) => Some(name.as_str()),
                    OpaqueTag::Builtin(_) | OpaqueTag::ProtocolTarget(_) => None,
                })
            })
            .flatten()
    }

    pub(super) fn as_builtin_opaque_singleton(&self) -> Option<BuiltinOpaque> {
        (!self.opaques.cofinite && self.opaques.values.len() == 1)
            .then(|| match self.opaques.values.iter().next() {
                Some(OpaqueTag::Builtin(builtin)) => Some(*builtin),
                _ => None,
            })
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

    /// Replacing a map field with the very same interned type changes no
    /// descriptor. Returning `None` keeps that proof at the structural owner,
    /// so callers can retain their existing `Ty` without rebuilding and
    /// re-interning this descriptor.
    pub(super) fn refine_map_field(&self, key: &MapKey, vt: Ty) -> Option<Descr> {
        let changed = self
            .maps
            .iter()
            .flat_map(|clause| clause.pos.iter())
            .any(|sig| sig.fields.get(key) != Some(&vt));
        if !changed {
            return None;
        }
        let mut out = self.clone();
        for clause in &mut out.maps {
            for sig in &mut clause.pos {
                sig.fields.insert(key.clone(), vt);
            }
        }
        Some(out)
    }

    /// This type read as ONE list signature, when it is purely a list and
    /// nothing else.
    ///
    /// `any_ty` is the caller's interned `any`, and it is what the axis TOP is
    /// read as: `types::axis` writes every axis's top as the clause with no
    /// factors, so the widest list carries no sig for this to borrow and the
    /// widest one has to be built. Every other clause shape answers from what
    /// it stores.
    pub(super) fn as_pure_list(&self, any_ty: Ty) -> Option<ListSig> {
        self.pure_axis(&self.lists, || ListSig {
            empty: true,
            elem: Some(any_ty),
        })
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

    /// This type read as ONE resource signature. `any_ty` spells the axis top's
    /// payload, for the reason [`as_pure_list`](Self::as_pure_list) states.
    pub(super) fn pure_resource(&self, any_ty: Ty) -> Option<ResourceSig> {
        self.pure_axis(&self.resources, || ResourceSig { payload: any_ty })
            .filter(|_| {
                self.tuples.is_empty() && self.lists.is_empty() && self.funcs.is_empty() && self.maps.is_empty()
            })
    }

    /// One axis's single clause read as one signature: the sig it stores, or
    /// `widest` where the clause is the axis's top and stores none.
    ///
    /// Only the list and resource axes have a `widest` to name. Every tuple is
    /// not one `TupleSig` (arity is unbounded), every map is not one `MapSig`
    /// (tags are), and every callable is not one `ArrowSig`, so the tuple, map
    /// and arrow readers below answer `None` for their axis top and are right
    /// to.
    fn pure_axis<T: Clone>(&self, clauses: &[Conj<T>], widest: impl FnOnce() -> T) -> Option<T> {
        if !self.axis_free() {
            return None;
        }
        match clauses {
            [clause] if clause.is_top() => Some(widest()),
            _ => single_positive(clauses).cloned(),
        }
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

    pub(super) fn pure_record(&self) -> Option<&MapSig> {
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

    /// A refinement of nothing is nothing, and a value carries at most one
    /// brand, so an empty brand slot (`Meters and Feet`) is empty too.
    ///
    /// Several DESCRIPTOR shapes reach the bottom — an empty slot over
    /// inhabited kind axes, empty kind axes under a slot still at top — and
    /// this is the test that recognizes all of them, so descriptor arithmetic
    /// can treat the bottom as the union identity before any id exists. After
    /// `Types::intern` those shapes are one interned identity, and
    /// `Types::is_empty(t)` holds exactly when `t` is `none()`.
    pub(super) fn looks_empty(&self) -> bool {
        looks_empty(self)
    }

    /// Whether this descriptor denotes EVERY value.
    ///
    /// [`looks_full`](Self::looks_full) proves it structurally and answers
    /// almost every ask, but it is INCOMPLETE: an axis can denote its whole
    /// kind without being written as its top. The callable axis is the one
    /// intern leaves unabsorbed (`types::axis` says why), so
    /// `(int) -> int ∨ ¬((int) -> int)` is every callable in two clauses, and
    /// a descriptor carrying it is `any` that does not look full. The semantic
    /// check behind it is reached only for a descriptor that already meets
    /// every necessary condition — every scalar axis saturated and every
    /// structural axis inhabited — which keeps the negation it costs off the
    /// common path. It mints nothing: the question is asked of descriptors.
    ///
    /// This is the ONE implementation of "is this everything". A structural
    /// answer alone reports a false difference wherever the two spellings of
    /// `any` diverge, and both the axis absorber and the canonical rendering
    /// ask it.
    pub(super) fn is_full(&self, cx: TyCtx<'_>) -> bool {
        if self.looks_full() {
            return true;
        }
        let saturated = self.basic == BasicBits::ALL
            && self.atoms.is_any()
            && self.opaques.is_any()
            && self.brands.is_any()
            && self.vars.is_any()
            && !self.tuples.is_empty()
            && !self.lists.is_empty()
            && !self.resources.is_empty()
            && !self.funcs.is_empty()
            && !self.maps.is_empty();
        saturated && Descr::any().is_subtype(cx, self)
    }

    /// The structural half of [`is_full`](Self::is_full): every axis written as
    /// its top. Sound, never complete — ask `is_full` unless the caller wants
    /// the spelling rather than the denotation.
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
    /// A BOTTOM is the identity first, before any of that. This runs on
    /// descriptors, BEFORE interning, and there the bottom has several shapes
    /// — a structural meet (`int and binary`) empties the kind axes and leaves
    /// the slot at top, a brand meet (`Meters and Feet`) empties the slot and
    /// leaves the kind axes inhabited. A pointwise hull would read an EMPTY
    /// operand's factors as constraints and widen the other side by them:
    /// `nothing | Meters(int)` would answer `int`.
    /// [`looks_empty`](Self::looks_empty) recognizes every shape, and asking
    /// it here is what keeps `∅ ∪ x = x` a law of the arithmetic rather than a
    /// property of the one identity interning later assigns.
    pub(super) fn union(&self, _cx: TyCtx<'_>, other: &Descr) -> Descr {
        union_of(self, other)
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
        // set — except at a bottom whose emptiness IS the empty slot
        // (`Meters and Feet` before interning), where releasing the slot would
        // resurrect the inner as a live `int` and tell the brand-blind runtime
        // question (`is_value_disjoint`) that an uninhabited type shares
        // values.
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
        // Nominals carry no embedded inner; erase conservatively.
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
