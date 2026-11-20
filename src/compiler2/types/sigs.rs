//! Structural signatures: `TupleSig`, `ListSig`, `ArrowSig`, `MapSig`,
//! the `ClosureLit` tag, and the `MergeSig` trait + per-sig impls.

use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;

use crate::fz_ir::FnId;

use super::{CallableValueKind, MapKey, Sigma, Ty, Types};

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct TupleSig {
    pub elems: Vec<Ty>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct ListSig {
    pub empty: bool,
    pub elem: Option<Ty>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct ResourceSig {
    pub payload: Ty,
}

impl ListSig {
    pub(super) fn empty() -> Self {
        Self {
            empty: true,
            elem: None,
        }
    }

    pub(super) fn possibly_empty(elem: Ty) -> Self {
        Self {
            empty: true,
            elem: Some(elem),
        }
    }

    pub(super) fn non_empty(elem: Ty) -> Self {
        Self {
            empty: false,
            elem: Some(elem),
        }
    }

    pub(super) fn is_exact_empty(&self) -> bool {
        self.empty && self.elem.is_none()
    }

    pub(super) fn is_exact_non_empty(&self) -> bool {
        !self.empty && self.elem.is_some()
    }

    pub(super) fn allow_empty(&mut self) {
        self.empty = true;
    }
}

/// fz-ul4.27.22.8 — closure-literal tag attached to an arrow clause.
/// When `ArrowSig::lit = Some(ClosureLit { kind, fn_id, captures })`, the
/// clause represents one specific callable value rather than only the
/// saturated arrow `(args)→ret`.
///
/// `kind = FnRef` means the value is a thin function reference with no
/// environment payload. `captures` must be empty in that case.
///
/// `kind = Closure` means the value is an env-carrying closure produced by
/// `MakeClosure(fn_id, vars_typed_as_captures)`. Captures are stored as a
/// vector aligned with the first N entry params of `fn_id`'s body.
///
/// The arrow's `args` field carries the apparent post-capture arity for
/// downstream contract-aware arrow matching.
///
/// Two `ClosureLit`s are equal iff `kind`, `fn_id`, and elementwise
/// `captures` match. Lit-bearing clauses do not collapse with lit-free clauses
/// under union — callable singletons are stricter than plain arrows, and the
/// union keeps both to preserve singleton precision downstream.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct ClosureLit {
    pub kind: CallableValueKind,
    /// The function the value was minted from, or `None` for an ANONYMOUS
    /// literal: a closure of SOME function closed over exactly these capture
    /// types, which is what a forwarder key leaves of a literal whose brand it
    /// erased (fz-6gb, fz-kdt.127). An anonymous literal contains every
    /// branded literal whose captures are inside its own, so it is never a
    /// singleton and never names a call target. A literal with nothing left to
    /// say — anonymous and capture-free — is not a literal at all: the erasure
    /// drops it and leaves the bare arrow.
    pub fn_id: Option<FnId>,
    pub captures: Vec<Ty>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct ArrowSig {
    pub args: Vec<Ty>,
    pub ret: Ty,
    /// `None` for ordinary arrows; `Some` for closure literals (fz-ul4.27.22.8).
    pub lit: Option<ClosureLit>,
}

/// The kind of a map key. A domain stands for every key of its kind that the
/// signature's fields do not name, so the kinds partition every possible key.
///
/// The set is Elixir's domain keys, with `port` replaced by the two key kinds
/// fz has in its place: `CPointer` and `Resource`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MapDomain {
    Atom,
    Binary,
    BitstringNoBinary,
    Integer,
    Float,
    Pid,
    Reference,
    CPointer,
    Fun,
    Tuple,
    Map,
    List,
    Resource,
}

impl MapDomain {
    pub(crate) const ALL: [MapDomain; 13] = [
        Self::Atom,
        Self::Binary,
        Self::BitstringNoBinary,
        Self::Integer,
        Self::Float,
        Self::Pid,
        Self::Reference,
        Self::CPointer,
        Self::Fun,
        Self::Tuple,
        Self::Map,
        Self::List,
        Self::Resource,
    ];

    /// The domain a literal key belongs to.
    pub(crate) fn of_key(key: &MapKey) -> Self {
        match key {
            MapKey::Atom(_) => Self::Atom,
            MapKey::Int(_) => Self::Integer,
        }
    }

    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Atom => "atom",
            Self::Binary => "binary",
            Self::BitstringNoBinary => "bitstring_no_binary",
            Self::Integer => "int",
            Self::Float => "float",
            Self::Pid => "pid",
            Self::Reference => "ref",
            Self::CPointer => "c_pointer",
            Self::Fun => "fun",
            Self::Tuple => "tuple",
            Self::Map => "map",
            Self::List => "list",
            Self::Resource => "resource",
        }
    }
}

/// One value type per [`MapDomain`]: what every key of that kind, outside the
/// signature's fields, maps to when it is present. A domain is never
/// required, so the empty map belongs to every domain assignment.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct MapDomains([Ty; 13]);

impl MapDomains {
    /// Every domain holds `value`.
    pub(crate) fn all(value: Ty) -> Self {
        Self([value; 13])
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (MapDomain, Ty)> + '_ {
        MapDomain::ALL.iter().map(|domain| (*domain, self[*domain]))
    }

    pub(crate) fn tys(&self) -> impl Iterator<Item = Ty> + '_ {
        self.0.iter().copied()
    }

    pub(crate) fn tys_mut(&mut self) -> impl Iterator<Item = &mut Ty> + '_ {
        self.0.iter_mut()
    }
}

impl std::ops::Index<MapDomain> for MapDomains {
    type Output = Ty;
    fn index(&self, domain: MapDomain) -> &Ty {
        &self.0[domain as usize]
    }
}

impl std::ops::IndexMut<MapDomain> for MapDomains {
    fn index_mut(&mut self, domain: MapDomain) -> &mut Ty {
        &mut self.0[domain as usize]
    }
}

/// What a map holds under one key: the value's type, and whether the key may
/// be absent. An optional field of type `none` is a key that must be absent.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct MapField {
    pub ty: Ty,
    pub optional: bool,
}

impl MapField {
    pub(crate) fn required(ty: Ty) -> Self {
        Self { ty, optional: false }
    }

    pub(crate) fn optional(ty: Ty) -> Self {
        Self { ty, optional: true }
    }
}

/// A map type, following Elixir's `Module.Types.Descr`: the maps in which
/// every key holds what this signature says it holds.
///
/// A key a field names holds that field's type, and the key is required
/// unless the field is optional. Every other key holds its kind's domain type
/// when present. A map type is open: a domain of `any` puts no limit on the
/// keys of its kind, so a signature of required fields with every domain
/// `any` is the open record of those fields, and no fields with every domain
/// `any` is every map.
///
/// Subtyping: `s <: t` iff every key `t` constrains is constrained at least as
/// tightly by `s`. More required keys, and narrower domains, mean a smaller
/// set.
#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct MapSig {
    pub fields: BTreeMap<MapKey, MapField>,
    pub domains: MapDomains,
}

impl MapSig {
    /// The open map holding exactly `fields`, with every domain `any`.
    pub(crate) fn open(fields: BTreeMap<MapKey, MapField>, any: Ty) -> Self {
        Self {
            fields,
            domains: MapDomains::all(any),
        }
    }

    /// What this map holds under `key`: the field that names it, or else the
    /// optional entry its kind's domain gives.
    pub(crate) fn field_at(&self, key: &MapKey) -> MapField {
        self.fields
            .get(key)
            .copied()
            .unwrap_or_else(|| MapField::optional(self.domains[MapDomain::of_key(key)]))
    }

    /// Every child type: the fields' values in key order, then the domains'.
    pub(crate) fn child_tys(&self) -> impl Iterator<Item = Ty> + '_ {
        self.fields.values().map(|field| field.ty).chain(self.domains.tys())
    }

    pub(crate) fn child_tys_mut(&mut self) -> impl Iterator<Item = &mut Ty> + '_ {
        self.fields
            .values_mut()
            .map(|field| &mut field.ty)
            .chain(self.domains.tys_mut())
    }

    /// Whether the map names `key` as a field it requires.
    pub(crate) fn requires(&self, key: &MapKey) -> bool {
        self.fields.get(key).is_some_and(|field| !field.optional)
    }
}

/// The outcome of intersecting two same-axis positive sigs inside one clause.
pub(crate) enum PosMeet<T> {
    /// The pair collapsed to one narrower sig (`A ∩ B` on this axis).
    Merged(T),
    /// The pair is provably disjoint, so the WHOLE clause (which conjoins
    /// both) is `∅` and must not persist.
    Empty,
    /// The pair cannot be collapsed or refuted structurally; the clause keeps
    /// both sigs as separate positive conjuncts.
    Distinct,
}

/// Same-shape positive clauses in an intersection should collapse to one
/// narrower clause. This keeps semantic meets stable instead of piling up
/// conjunctive structure on every repeated refinement, and lets a merge that
/// proves emptiness drop the clause instead of persisting garbage (fz-go4.24).
pub(crate) trait MergeSig: Clone + PartialEq {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self>;
}

impl MergeSig for ListSig {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        let elem = match (a.elem, b.elem) {
            (Some(a), Some(b)) => {
                let elem = types.intersect(a, b);
                if types.is_empty(&elem) { None } else { Some(elem) }
            }
            _ => None,
        };
        let empty = a.empty && b.empty;
        // A non-empty list needs a head in the element intersection; with no
        // element left and `[]` excluded, the merged sig denotes `∅`.
        if !empty && elem.is_none() {
            return PosMeet::Empty;
        }
        PosMeet::Merged(ListSig { empty, elem })
    }
}

impl MergeSig for ResourceSig {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        // `res(A) ∩ res(B) = res(A ∩ B)`, and `res(∅) = ∅` (a resource always
        // carries a payload; `Types::resource` refuses an empty one).
        let payload = types.intersect(a.payload, b.payload);
        if types.is_empty(&payload) {
            PosMeet::Empty
        } else {
            PosMeet::Merged(ResourceSig { payload })
        }
    }
}

impl MergeSig for TupleSig {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        // Tuples of different arity are disjoint products: `A₁×…×Aₙ ∩
        // B₁×…×Bₘ = ∅` for `n ≠ m` (a tuple value has exactly one arity —
        // the same rule `emptiness::tuple_clause_empty` decides by).
        if a.elems.len() != b.elems.len() {
            return PosMeet::Empty;
        }
        // `∏Aᵢ ∩ ∏Bᵢ = ∏(Aᵢ ∩ Bᵢ)`; a product with an empty factor is `∅`.
        let elems: Vec<Ty> = a
            .elems
            .iter()
            .zip(b.elems.iter())
            .map(|(x, y)| types.intersect(*x, *y))
            .collect();
        if elems.iter().any(|e| types.is_empty(e)) {
            return PosMeet::Empty;
        }
        PosMeet::Merged(TupleSig { elems })
    }
}

impl MergeSig for ArrowSig {
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        // A function takes one number of arguments, so arrows of different
        // arities share no function -- the rule `emptiness::func_clause_empty`
        // decides by. Arrows of one arity that do not merge stay Distinct: a
        // conjunction of them is an overload, which is inhabited in general.
        if a.args.len() != b.args.len() {
            return PosMeet::Empty;
        }
        match (&a.lit, &b.lit) {
            (Some(la), Some(lb)) => {
                // An anonymous literal is every brand at once, so meeting it
                // with a branded one keeps the brand; two brands that differ
                // name disjoint values and stay Distinct.
                let fn_id = match (la.fn_id, lb.fn_id) {
                    (Some(a), Some(b)) if a != b => return PosMeet::Distinct,
                    (Some(a), _) => Some(a),
                    (None, b) => b,
                };
                if la.kind != lb.kind || la.captures.len() != lb.captures.len() {
                    return PosMeet::Distinct;
                }
                PosMeet::Merged(ArrowSig {
                    args: a
                        .args
                        .iter()
                        .zip(b.args.iter())
                        .map(|(x, y)| types.union(*x, *y))
                        .collect(),
                    ret: types.intersect(a.ret, b.ret),
                    lit: Some(ClosureLit {
                        kind: la.kind,
                        fn_id,
                        captures: la
                            .captures
                            .iter()
                            .zip(lb.captures.iter())
                            .map(|(x, y)| types.intersect(*x, *y))
                            .collect(),
                    }),
                })
            }
            (Some(_), None) | (None, Some(_)) => {
                let (literal, surface) = if a.lit.is_some() { (a, b) } else { (b, a) };
                let (args, ret) = specialize_surface(types, (&literal.args, literal.ret), (&surface.args, surface.ret));
                PosMeet::Merged(ArrowSig {
                    args,
                    ret,
                    lit: literal.lit.clone(),
                })
            }
            (None, None) => PosMeet::Merged(ArrowSig {
                args: a
                    .args
                    .iter()
                    .zip(b.args.iter())
                    .map(|(x, y)| types.union(*x, *y))
                    .collect(),
                ret: types.intersect(a.ret, b.ret),
                lit: None,
            }),
        }
    }
}

/// One callable read at the surface it is being viewed through: the
/// substitution its own params and result take against that surface, applied
/// to them.
///
/// A closure literal is minted carrying the surface vars its lambda owns, and
/// every caller meets it with the surface its callsite states. The two meet in
/// two places -- at CONSTRUCTION, where a positive meet folds a lit-free arrow
/// into a literal's clause, and on READ, where `Types::callable_value_clauses`
/// views a literal through a surface clause standing beside it -- and this is
/// the whole computation both times, so neither can report a different shape
/// for one literal at one surface.
///
/// Positions past the shorter side are not substituted through; every caller
/// has already required the two arities to agree.
pub(super) fn specialize_surface(types: &mut Types, callable: (&[Ty], Ty), surface: (&[Ty], Ty)) -> (Vec<Ty>, Ty) {
    let (params, result) = callable;
    let (witness_params, witness_result) = surface;
    let mut sigma = Sigma::default();
    for (pattern, witness) in params.iter().zip(witness_params.iter()) {
        types.collect_instantiation_subst(pattern, witness, &mut sigma);
    }
    types.collect_instantiation_subst(&result, &witness_result, &mut sigma);
    (
        params.iter().map(|param| types.instantiate(param, &sigma)).collect(),
        types.instantiate(&result, &sigma),
    )
}

impl MergeSig for MapSig {
    // A key holds the intersection of what each side holds under it, where a
    // side that does not name the key holds its kind's domain; the key is
    // optional only if both sides leave it optional. The domains intersect
    // kind by kind.
    //
    // Always `Merged`, never `Empty`: a required field intersected to `∅`
    // (an uninhabited required field) makes the whole merged clause `∅` and
    // ought to drop rather than persist, mirroring `TupleSig`'s empty-
    // coordinate rule. Measured and left unfixed: an intern-smell probe (the
    // same method that justified the tuples-axis fix) instrumented every
    // `Types::intern` call for
    // duplicate, provably-empty, or subsumed map clauses and found zero
    // across the full fixture census and the lib suite — no live map DNF
    // ever carries the garbage this would need to catch. Paying per-field
    // emptiness on every map intersect to canonicalize an axis that stays
    // clean in practice is not justified without a measured blowup (the
    // tuples-axis fix was justified by one: a 60-clause tuple DNF with 54
    // provably-empty clauses). Re-measure before adding this if map-heavy
    // evidence-join traffic starts to matter.
    fn intersect_pos(types: &mut Types, a: &Self, b: &Self) -> PosMeet<Self> {
        let keys: BTreeSet<&MapKey> = a.fields.keys().chain(b.fields.keys()).collect();
        let mut fields = BTreeMap::new();
        for key in keys {
            let (ours, theirs) = (a.field_at(key), b.field_at(key));
            fields.insert(
                key.clone(),
                MapField {
                    ty: types.intersect(ours.ty, theirs.ty),
                    optional: ours.optional && theirs.optional,
                },
            );
        }
        let mut domains = a.domains;
        for domain in MapDomain::ALL {
            domains[domain] = types.intersect(a.domains[domain], b.domains[domain]);
        }
        PosMeet::Merged(MapSig { fields, domains })
    }
}
