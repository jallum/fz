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
    pub(super) cases: Vec<BrandCase<R>>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(super) struct BrandCase<R> {
    pub(super) brands: FiniteSet<String>,
    pub(super) structure: StructureOf<R>,
}

/// The non-brand axes of one correlated brand case. A `DescrOf` owns only a
/// finite/cofinite partition of these payloads; no valid descriptor carries a
/// global brand factor beside independently-unioned structural axes.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(super) struct StructureOf<R> {
    pub(super) basic: BasicBits,
    pub(super) atoms: AtomSet,
    pub(super) opaques: FiniteSet<OpaqueTag>,
    pub(super) vars: VarSet,
    pub(super) tuples: Vec<Conj<TupleSigOf<R>>>,
    pub(super) lists: Vec<Conj<ListSigOf<R>>>,
    pub(super) resources: Vec<Conj<ResourceSigOf<R>>>,
    pub(super) funcs: Vec<Conj<ArrowSigOf<R>>>,
    pub(super) maps: Vec<Conj<MapSigOf<R>>>,
}

pub(super) type Descr = DescrOf<Ty>;
pub(super) type Structure = StructureOf<Ty>;

pub(crate) fn union_of<R: Clone + PartialEq>(left: &DescrOf<R>, right: &DescrOf<R>) -> DescrOf<R> {
    // The unrefined subset has exactly one brand cell. Preserve its old raw
    // structural union before the interner's cheap lookup: concatenating two
    // `any` cells would force a normalization miss even when that structural
    // union is already interned. Correlated inputs deliberately take the
    // general case below and are canonicalized only by
    // `canonical_brand_partition` at the persistence boundary.
    if !left.cases.is_empty()
        && !right.cases.is_empty()
        && left.cases.iter().chain(&right.cases).all(|case| case.brands.is_any())
    {
        let structure = left
            .cases
            .iter()
            .chain(&right.cases)
            .fold(StructureOf::none(), |structure, case| {
                structure.union_raw(&case.structure)
            });
        return DescrOf {
            cases: vec![BrandCase {
                brands: FiniteSet::any(),
                structure,
            }],
        };
    }
    let mut cases = left.cases.clone();
    cases.extend(right.cases.clone());
    DescrOf { cases }
}

/// The sole brand-partition construction used by both ground and regular
/// descriptors.  Callers supply their child-domain normalization; this helper
/// never asks semantic emptiness, so unresolved component references stay
/// cycle-safe.
pub(super) fn canonical_brand_partition<R: Clone + PartialEq + Ord>(
    d: DescrOf<R>,
    mut normalize: impl FnMut(&mut StructureOf<R>),
) -> DescrOf<R> {
    // The common unrefined path is one residual cell. It is still normalized
    // through this authority, but needs neither named-cell carving nor payload
    // grouping to prove its canonical spelling.
    if d.cases.iter().all(|case| case.brands.is_any()) {
        let mut structure = StructureOf::none();
        for case in d.cases {
            structure = structure.union_raw(&case.structure);
        }
        normalize(&mut structure);
        return if structure_looks_empty(&structure) {
            DescrOf { cases: Vec::new() }
        } else {
            DescrOf {
                cases: vec![BrandCase {
                    brands: FiniteSet::any(),
                    structure,
                }],
            }
        };
    }
    let names = d
        .cases
        .iter()
        .flat_map(|case| case.brands.values.iter().cloned())
        .collect::<std::collections::BTreeSet<_>>();
    let mut cells = Vec::new();
    for name in &names {
        let mut payload = StructureOf::none();
        for case in &d.cases {
            if case.brands.contains(name) {
                payload = payload.union_raw(&case.structure);
            }
        }
        normalize(&mut payload);
        if !structure_looks_empty(&payload) {
            cells.push((name.clone(), payload));
        }
    }
    let mut residual = StructureOf::none();
    for case in &d.cases {
        if case.brands.cofinite {
            residual = residual.union_raw(&case.structure);
        }
    }
    normalize(&mut residual);
    let residual = (!structure_looks_empty(&residual)).then_some(residual);
    let mut grouped = std::collections::BTreeMap::<StructureOf<R>, std::collections::BTreeSet<String>>::new();
    for (name, payload) in cells {
        grouped.entry(payload).or_default().insert(name);
    }
    let mut cases = Vec::new();
    for (payload, included) in grouped {
        let brands = if residual.as_ref() == Some(&payload) {
            FiniteSet::cofinite(names.iter().filter(|name| !included.contains(*name)).cloned())
        } else {
            FiniteSet::finite(included)
        };
        cases.push(BrandCase {
            brands,
            structure: payload,
        });
    }
    if let Some(payload) = residual
        && !cases.iter().any(|case| case.structure == payload)
    {
        cases.push(BrandCase {
            brands: FiniteSet::cofinite(names),
            structure: payload,
        });
    }
    cases.sort();
    DescrOf { cases }
}

fn structure_looks_empty<R>(body: &StructureOf<R>) -> bool {
    body.basic.is_empty()
        && body.atoms.is_none()
        && body.opaques.is_none()
        && body.vars.is_none()
        && body.tuples.is_empty()
        && body.lists.is_empty()
        && body.resources.is_empty()
        && body.funcs.is_empty()
        && body.maps.is_empty()
}

impl<R: Clone> DescrOf<R> {
    fn leaf(structure: StructureOf<R>) -> Self {
        Self {
            cases: vec![BrandCase {
                brands: FiniteSet::any(),
                structure,
            }],
        }
    }

    fn leaf_mut(&mut self) -> &mut StructureOf<R> {
        match self.cases.as_mut_slice() {
            [BrandCase { brands, structure }] if brands.is_any() => structure,
            _ => panic!("a value constructor must begin from one unconstrained brand case"),
        }
    }

    pub(crate) fn any() -> Self {
        Self::leaf(StructureOf::any())
    }
}

impl<R> StructureOf<R> {
    pub(super) fn any() -> Self {
        Self {
            basic: BasicBits::ALL,
            atoms: AtomSet::any(),
            opaques: FiniteSet::any(),
            vars: VarSet::any(),
            tuples: vec![Conj::top()],
            lists: vec![Conj::top()],
            resources: vec![Conj::top()],
            funcs: vec![Conj::top()],
            maps: vec![Conj::top()],
        }
    }

    pub(super) fn none() -> Self {
        Self {
            basic: BasicBits::NONE,
            atoms: AtomSet::none(),
            opaques: FiniteSet::none(),
            vars: VarSet::none(),
            tuples: Vec::new(),
            lists: Vec::new(),
            resources: Vec::new(),
            funcs: Vec::new(),
            maps: Vec::new(),
        }
    }
}

impl<R: Clone + PartialEq> StructureOf<R> {
    /// Structural union before a caller's child-domain-specific normalization.
    /// It is shared by ground interning and regular-component construction;
    /// neither path may manufacture a second brand-partition meaning.
    pub(super) fn union_raw(&self, other: &Self) -> Self {
        Self {
            basic: self.basic.union(other.basic),
            atoms: self.atoms.union(&other.atoms),
            opaques: self.opaques.union(&other.opaques),
            vars: self.vars.union(&other.vars),
            tuples: dnf_union(&self.tuples, &other.tuples),
            lists: dnf_union(&self.lists, &other.lists),
            resources: dnf_union(&self.resources, &other.resources),
            funcs: dnf_union(&self.funcs, &other.funcs),
            maps: dnf_union(&self.maps, &other.maps),
        }
    }
}

impl<R: Clone> DescrOf<R> {
    /// The builder base for a VALUE constructor: one unconstrained brand case
    /// with no structural content yet. `brands` is a conjunctive REFINEMENT
    /// factor, not a kind of value — an unbranded `int` admits a branded int
    /// (`Meters <: int`), while `Descr::none()` has no cases at all.
    pub(crate) fn unbranded() -> Self {
        Self::leaf(StructureOf::none())
    }

    pub(crate) fn none() -> Self {
        Self { cases: Vec::new() }
    }

    pub(crate) fn opaque_of(name: impl Into<String>) -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().opaques = FiniteSet::lit(OpaqueTag::Named(name.into()));
        d
    }

    pub(crate) fn builtin_opaque(builtin: BuiltinOpaque) -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().opaques = FiniteSet::lit(OpaqueTag::Builtin(builtin));
        d
    }

    pub(super) fn struct_map(tag: StructTag, fields: BTreeMap<MapKey, R>) -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().maps.push(Conj::pos_of(MapSigOf {
            tag: MapTag::Struct(tag),
            fields,
        }));
        d
    }

    pub(super) fn record(tag: MapTag, fields: impl IntoIterator<Item = (MapKey, R)>) -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().maps.push(Conj::pos_of(MapSigOf {
            tag,
            fields: fields.into_iter().collect(),
        }));
        d
    }

    pub(crate) fn var(id: TypeVarId) -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().vars = VarSet::lit(id);
        d
    }

    pub(crate) fn nil() -> Self {
        Self::atom_lit("nil")
    }

    pub(crate) fn bool_t() -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().atoms = AtomSet::lit("true".to_string()).union(&AtomSet::lit("false".to_string()));
        d
    }

    pub(crate) fn atom_top() -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().atoms = AtomSet::any();
        d
    }

    /// The top of the function axis — "any callable", with no other axis. The
    /// canonical value-lane representative for every callable value: a callable's
    /// runtime layout is one word (a code pointer or a closure ref) regardless of
    /// signature or identity, so every callable shares this one lane.
    pub(crate) fn fun_top() -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().funcs = vec![Conj::top()];
        d
    }

    pub(crate) fn atom_lit(name: impl Into<String>) -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().atoms = AtomSet::lit(name.into());
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
        d.leaf_mut().basic = basic;
        d
    }

    pub(crate) fn resource_of(payload: R) -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().resources = vec![Conj::pos_of(ResourceSigOf { payload })];
        d
    }

    pub(crate) fn tuple_of(elems: Vec<R>) -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().tuples.push(Conj::pos_of(TupleSigOf { elems }));
        d
    }

    pub(crate) fn list_sig(sig: ListSigOf<R>) -> Self {
        let mut d = Self::unbranded();
        d.leaf_mut().lists.push(Conj::pos_of(sig));
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
        d.leaf_mut().funcs.push(Conj::pos_of(ArrowSigOf {
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
        d.leaf_mut().maps.push(Conj::pos_of(MapSigOf {
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
            cases: self
                .cases
                .into_iter()
                .map(|BrandCase { brands, structure }| BrandCase {
                    brands,
                    structure: StructureOf {
                        basic: structure.basic,
                        atoms: structure.atoms,
                        opaques: structure.opaques,
                        vars: structure.vars,
                        tuples: map_clauses(structure.tuples, |sig| TupleSigOf {
                            elems: sig.elems.into_iter().map(&mut map).collect(),
                        }),
                        lists: map_clauses(structure.lists, |sig| ListSigOf {
                            empty: sig.empty,
                            elem: sig.elem.map(&mut map),
                        }),
                        resources: map_clauses(structure.resources, |sig| ResourceSigOf {
                            payload: map(sig.payload),
                        }),
                        funcs: map_clauses(structure.funcs, |sig| ArrowSigOf {
                            args: sig.args.into_iter().map(&mut map).collect(),
                            ret: map(sig.ret),
                            lit: sig.lit.map(|lit| ClosureLitOf {
                                kind: lit.kind,
                                fn_id: lit.fn_id,
                                captures: lit.captures.into_iter().map(&mut map).collect(),
                            }),
                        }),
                        maps: map_clauses(structure.maps, |sig| MapSigOf {
                            tag: sig.tag,
                            fields: sig.fields.into_iter().map(|(key, value)| (key, map(value))).collect(),
                        }),
                    },
                })
                .collect(),
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

impl StructureOf<Ty> {
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
    pub(super) fn as_tuple_singleton(&self) -> Option<&[Ty]> {
        if self.basic.is_empty()
            && self.atoms.is_none()
            && self.opaques.is_none()
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
    pub(super) fn refine_map_field(&self, key: &MapKey, vt: Ty) -> Option<Structure> {
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

    /// The structural alternatives of one already-correlated case.  The outer
    /// descriptor reinstates this case's brand cell around every result; a
    /// structural projection must never turn a branded shape into its
    /// unbranded hull.
    fn projection_alternatives(&self) -> Option<Vec<Structure>> {
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
                    .map(|clause| Structure {
                        tuples: vec![clause],
                        ..Structure::none()
                    })
                    .collect(),
            );
        }
        if self.lists.len() > 1 {
            return Some(
                self.lists
                    .iter()
                    .cloned()
                    .map(|clause| Structure {
                        lists: vec![clause],
                        ..Structure::none()
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
        self.basic.is_empty() && self.atoms.is_none() && self.opaques.is_none() && self.vars.is_none()
    }

    /// Structural bottom: no axis admits any value. The outer descriptor also
    /// treats a case with an empty brand set as empty; that question belongs to
    /// `DescrOf::looks_empty`, not to its non-brand payload.
    pub(super) fn looks_empty(&self) -> bool {
        structure_looks_empty(self)
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
            && self.vars.is_any()
            && !self.tuples.is_empty()
            && !self.lists.is_empty()
            && !self.resources.is_empty()
            && !self.funcs.is_empty()
            && !self.maps.is_empty();
        saturated && Structure::any().is_subtype(cx, self)
    }

    /// The structural half of [`is_full`](Self::is_full): every axis written as
    /// its top. Sound, never complete — ask `is_full` unless the caller wants
    /// the spelling rather than the denotation.
    pub(super) fn looks_full(&self) -> bool {
        self.basic == BasicBits::ALL
            && self.atoms.is_any()
            && self.opaques.is_any()
            && self.vars.is_any()
            && is_dnf_top(&self.tuples)
            && is_dnf_top(&self.lists)
            && is_dnf_top(&self.resources)
            && is_dnf_top(&self.funcs)
            && is_dnf_top(&self.maps)
    }

    /// Union of structural payloads from already-selected brand cells. The
    /// outer descriptor owns correlation: it appends cases and the interning
    /// partitioner merges payloads only for the same admitted brand cell.
    pub(super) fn union(&self, _cx: TyCtx<'_>, other: &Structure) -> Structure {
        self.union_raw(other)
    }

    /// Exact meet of two structural payloads. The outer descriptor meets their
    /// brand sets separately, preserving the one-brand-per-value rule.
    pub(super) fn intersect(&self, other: &Structure) -> Structure {
        Structure {
            basic: self.basic.intersect(other.basic),
            atoms: self.atoms.intersect(&other.atoms),
            opaques: self.opaques.intersect(&other.opaques),
            vars: self.vars.intersect(&other.vars),
            tuples: dnf_intersect(&self.tuples, &other.tuples),
            lists: dnf_intersect(&self.lists, &other.lists),
            resources: dnf_intersect(&self.resources, &other.resources),
            funcs: dnf_intersect(&self.funcs, &other.funcs),
            maps: dnf_intersect(&self.maps, &other.maps),
        }
    }

    /// The complement of one case's structural union. Outer descriptor
    /// difference composes this with the brand partition, retaining both the
    /// structural outside and the overlapping structure under remaining brands.
    fn neg_structure(&self) -> Structure {
        Structure {
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

    /// Structural subtraction for one rectangle.  Outer descriptor difference
    /// keeps both rectangles in `(S, B) \ (S', B') = (S \ S', B) ∪
    /// (S ∩ S', B \ B')`; this helper deliberately handles only the first.
    pub(super) fn diff(&self, other: &Structure) -> Structure {
        self.intersect(&other.neg_structure())
    }

    fn as_all_brands(&self) -> Descr {
        Descr {
            cases: vec![BrandCase {
                brands: FiniteSet::any(),
                structure: self.clone(),
            }],
        }
    }

    pub(super) fn is_empty(&self, cx: TyCtx<'_>) -> bool {
        self.as_all_brands().is_empty(cx)
    }

    /// The one structural emptiness reader.  `DescrOf::is_empty_memo` owns the
    /// recursion guard because recursive child references are descriptors;
    /// each admitted brand cell only delegates its non-brand axes here.
    fn axes_are_empty(&self, cx: TyCtx<'_>, memo: &mut Memo) -> bool {
        self.basic.is_empty()
            && self.atoms.is_none()
            && self.opaques.is_none()
            && self.vars.is_none()
            && self.tuples.iter().all(|c| tuple_clause_empty(cx, c, memo))
            && self.lists.iter().all(|c| list_clause_empty(cx, c, memo))
            && self.resources.iter().all(|c| resource_clause_empty(cx, c, memo))
            && self.funcs.iter().all(|c| func_clause_empty(cx, c, memo))
            && self.maps.iter().all(|c| map_clause_empty(cx, c, memo))
    }

    pub(super) fn is_subtype(&self, cx: TyCtx<'_>, other: &Structure) -> bool {
        self.diff(other).is_empty(cx)
    }

    pub(super) fn value_disjoint(&self, cx: TyCtx<'_>, other: &Structure) -> bool {
        self.erase_nominal(cx).intersect(&other.erase_nominal(cx)).is_empty(cx)
    }

    fn erase_nominal(&self, cx: TyCtx<'_>) -> Structure {
        // This helper owns only structural axes. Brand erasure is expressed by
        // `DescrOf::value_disjoint` selecting structures without consulting
        // their enclosing case's brand set.
        if self.looks_empty() {
            return Structure::none();
        }
        let mut d = self.clone();
        // Opaques have no structural inner, so their erasure is conservative.
        let opaques = std::mem::replace(&mut d.opaques, FiniteSet::none());
        // Nominals carry no embedded inner; erase conservatively.
        if !opaques.is_none() {
            d = d.union(cx, &Structure::any());
        }
        d
    }
}

impl DescrOf<Ty> {
    fn common_ref<'a, T: PartialEq + ?Sized>(&'a self, read: impl Fn(&'a Structure) -> Option<&'a T>) -> Option<&'a T> {
        let (first, rest) = self.cases.split_first()?;
        let value = read(&first.structure)?;
        rest.iter()
            .all(|case| read(&case.structure) == Some(value))
            .then_some(value)
    }

    fn common_owned<T: Clone + PartialEq>(&self, read: impl Fn(&Structure) -> Option<T>) -> Option<T> {
        let (first, rest) = self.cases.split_first()?;
        let value = read(&first.structure)?;
        rest.iter()
            .all(|case| read(&case.structure).as_ref() == Some(&value))
            .then_some(value)
    }

    pub(super) fn as_atom_singleton(&self) -> Option<&str> {
        self.common_ref(Structure::as_atom_singleton)
    }

    pub(super) fn atom_literals(&self) -> Option<Vec<String>> {
        let mut literals = AtomSet::none();
        for case in &self.cases {
            let atoms = case.structure.atom_literals()?;
            literals = literals.union(&AtomSet::finite(atoms));
        }
        (!literals.cofinite).then(|| literals.values.into_iter().collect())
    }

    pub(super) fn as_opaque_singleton(&self) -> Option<&str> {
        self.common_ref(Structure::as_opaque_singleton)
    }

    pub(super) fn as_builtin_opaque_singleton(&self) -> Option<BuiltinOpaque> {
        self.common_owned(Structure::as_builtin_opaque_singleton)
    }

    #[cfg(test)]
    pub(super) fn as_brand_singleton(&self) -> Option<&str> {
        let [case] = self.cases.as_slice() else {
            return None;
        };
        (!case.brands.cofinite && case.brands.values.len() == 1)
            .then(|| case.brands.values.iter().next().map(String::as_str))
            .flatten()
    }

    #[cfg(test)]
    pub(super) fn as_tuple_singleton(&self) -> Option<&[Ty]> {
        self.common_ref(Structure::as_tuple_singleton)
    }

    pub(super) fn as_closure_lit(&self) -> Option<&ClosureLit> {
        self.common_ref(Structure::as_closure_lit)
    }

    pub(super) fn is_singleton_literal(&self) -> bool {
        self.as_atom_singleton().is_some()
    }

    pub(super) fn max_tuple_arity(&self) -> usize {
        self.cases
            .iter()
            .map(|case| case.structure.max_tuple_arity())
            .max()
            .unwrap_or(0)
    }

    pub(super) fn refine_map_field(&self, key: &MapKey, vt: Ty) -> Option<Descr> {
        let mut changed = false;
        let cases = self
            .cases
            .iter()
            .map(|case| {
                let structure = match case.structure.refine_map_field(key, vt) {
                    Some(structure) => {
                        changed = true;
                        structure
                    }
                    None => case.structure.clone(),
                };
                BrandCase {
                    brands: case.brands.clone(),
                    structure,
                }
            })
            .collect();
        changed.then_some(Descr { cases })
    }

    pub(super) fn as_pure_list(&self, any_ty: Ty) -> Option<ListSig> {
        self.common_owned(|structure| structure.as_pure_list(any_ty))
    }

    pub(super) fn is_pure_list_family(&self) -> bool {
        !self.cases.is_empty() && self.cases.iter().all(|case| case.structure.is_pure_list_family())
    }

    pub(super) fn projection_alternatives(&self) -> Option<Vec<Descr>> {
        let mut alternatives = Vec::new();
        for case in &self.cases {
            let structures = case.structure.projection_alternatives()?;
            alternatives.extend(structures.into_iter().map(|structure| Descr {
                cases: vec![BrandCase {
                    brands: case.brands.clone(),
                    structure,
                }],
            }));
        }
        Some(alternatives)
    }

    pub(super) fn pure_tuple(&self) -> Option<&TupleSig> {
        self.common_ref(Structure::pure_tuple)
    }

    pub(super) fn pure_resource(&self, any_ty: Ty) -> Option<ResourceSig> {
        self.common_owned(|structure| structure.pure_resource(any_ty))
    }

    pub(super) fn pure_arrow(&self) -> Option<&ArrowSig> {
        self.common_ref(Structure::pure_arrow)
    }

    pub(super) fn pure_record(&self) -> Option<&MapSig> {
        self.common_ref(Structure::pure_record)
    }

    pub(super) fn is_pure_callable(&self) -> bool {
        !self.cases.is_empty() && self.cases.iter().all(|case| case.structure.is_pure_callable())
    }

    pub(super) fn looks_empty(&self) -> bool {
        self.cases.is_empty()
            || self
                .cases
                .iter()
                .all(|case| case.brands.is_none() || case.structure.looks_empty())
    }

    pub(super) fn looks_full(&self) -> bool {
        self.cases
            .iter()
            .filter(|case| case.structure.looks_full())
            .fold(FiniteSet::none(), |covered, case| covered.union(&case.brands))
            .is_any()
    }

    pub(super) fn is_full(&self, cx: TyCtx<'_>) -> bool {
        self.cases
            .iter()
            .filter(|case| case.structure.is_full(cx))
            .fold(FiniteSet::none(), |covered, case| covered.union(&case.brands))
            .is_any()
    }

    pub(super) fn union(&self, _cx: TyCtx<'_>, other: &Descr) -> Descr {
        union_of(self, other)
    }

    pub(super) fn intersect(&self, other: &Descr) -> Descr {
        let mut cases = Vec::new();
        for left in &self.cases {
            for right in &other.cases {
                let brands = left.brands.intersect(&right.brands);
                if !brands.is_none() {
                    cases.push(BrandCase {
                        brands,
                        structure: left.structure.intersect(&right.structure),
                    });
                }
            }
        }
        Descr { cases }
    }

    pub(super) fn diff(&self, other: &Descr) -> Descr {
        let mut cases = self.cases.clone();
        for subtrahend in &other.cases {
            let mut next = Vec::new();
            for minuend in cases {
                let outside = minuend.structure.diff(&subtrahend.structure);
                if !outside.looks_empty() {
                    next.push(BrandCase {
                        brands: minuend.brands.clone(),
                        structure: outside,
                    });
                }
                let brands = minuend.brands.intersect(&subtrahend.brands.neg());
                let overlap = minuend.structure.intersect(&subtrahend.structure);
                if !brands.is_none() && !overlap.looks_empty() {
                    next.push(BrandCase {
                        brands,
                        structure: overlap,
                    });
                }
            }
            cases = next;
        }
        Descr { cases }
    }

    pub(super) fn is_empty(&self, cx: TyCtx<'_>) -> bool {
        let mut memo = Memo::default();
        self.is_empty_memo(cx, &mut memo)
    }

    pub(super) fn is_empty_memo(&self, cx: TyCtx<'_>, memo: &mut Memo) -> bool {
        memo.query_descr(self, |memo| cases_are_empty(self, cx, memo))
    }

    pub(super) fn is_subtype(&self, cx: TyCtx<'_>, other: &Descr) -> bool {
        self.diff(other).is_empty(cx)
    }

    pub(super) fn is_equiv(&self, cx: TyCtx<'_>, other: &Descr) -> bool {
        self == other || (self.is_subtype(cx, other) && other.is_subtype(cx, self))
    }

    pub(super) fn value_disjoint(&self, cx: TyCtx<'_>, other: &Descr) -> bool {
        self.cases.iter().all(|left| {
            other
                .cases
                .iter()
                .all(|right| left.structure.value_disjoint(cx, &right.structure))
        })
    }
}

/// Every admitted brand case's non-brand axes, read off one already-resolved
/// descriptor. The one place `is_empty_memo`'s two entry points (a `Descr`
/// already in hand, or a bare `Ty` still to resolve) agree on what "empty"
/// means, so neither can drift from the other.
fn cases_are_empty(d: &Descr, cx: TyCtx<'_>, memo: &mut Memo) -> bool {
    d.cases
        .iter()
        .all(|case| case.brands.is_none() || case.structure.axes_are_empty(cx, memo))
}

/// [`DescrOf::is_empty_memo`] for a `Ty` nothing has touched yet: the memo
/// keys this on the id itself (see [`Memo::query_ty`]) instead of cloning
/// the descriptor it resolves to just to ask a question about it.
pub(super) fn is_empty_memo_ty(ty: Ty, cx: TyCtx<'_>, memo: &mut Memo) -> bool {
    memo.query_ty(ty, |memo| cases_are_empty(cx.descr(&ty), cx, memo))
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
