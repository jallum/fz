//! Private descriptor for the interned type implementation.

use super::bits::BasicBits;
use super::conj::Conj;
use super::dnf::{dnf_intersect, dnf_neg, dnf_union, is_dnf_top, normalize_empty_nonempty_list_unions};
use super::emptiness::{
    Memo, func_clause_empty, list_clause_empty, map_clause_empty, resource_clause_empty, tuple_clause_empty,
};
use super::lit_set::{AtomSet, LiteralSet, VarSet};
use super::sigs::{ArrowSig, ClosureLit, ListSig, MapSig, ResourceSig, TupleSig};
use super::{MapKey, Ty, TyCtx, TypeVarId};

#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct Descr {
    pub(super) basic: BasicBits,
    pub(super) atoms: AtomSet,
    pub(super) opaques: LiteralSet<String>,
    pub(super) brands: LiteralSet<String>,
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
            opaques: LiteralSet::any(),
            brands: LiteralSet::any(),
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
            opaques: LiteralSet::none(),
            brands: LiteralSet::none(),
            vars: VarSet::none(),
            tuples: Vec::new(),
            lists: Vec::new(),
            resources: Vec::new(),
            funcs: Vec::new(),
            maps: Vec::new(),
        }
    }

    pub(super) fn opaque_of(name: impl Into<String>) -> Self {
        let mut d = Self::none();
        d.opaques = LiteralSet::lit(name.into());
        d
    }

    pub(super) fn brand_of(name: impl Into<String>) -> Self {
        let mut d = Self::none();
        d.brands = LiteralSet::lit(name.into());
        d
    }

    pub(super) fn var(id: TypeVarId) -> Self {
        let mut d = Self::none();
        d.vars = LiteralSet::lit(id);
        d
    }

    pub(super) fn nil() -> Self {
        Self::atom_lit("nil")
    }

    pub(super) fn bool_t() -> Self {
        let mut d = Self::none();
        d.atoms = AtomSet::lit("true".to_string()).union(&AtomSet::lit("false".to_string()));
        d
    }

    pub(super) fn atom_top() -> Self {
        let mut d = Self::none();
        d.atoms = AtomSet::any();
        d
    }

    pub(super) fn atom_lit(name: impl Into<String>) -> Self {
        let mut d = Self::none();
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
        let mut d = Self::none();
        d.basic = basic;
        d
    }

    pub(super) fn resource_of(cx: TyCtx<'_>, payload: Ty) -> Self {
        if cx.descr(&payload).is_empty(cx) {
            return Self::none();
        }
        let mut d = Self::none();
        d.resources = vec![Conj::pos_of(ResourceSig { payload })];
        d
    }

    pub(super) fn tuple_of(elems: impl IntoIterator<Item = Ty>) -> Self {
        let mut d = Self::none();
        d.tuples.push(Conj::pos_of(TupleSig {
            elems: elems.into_iter().collect(),
        }));
        d
    }

    pub(super) fn list_sig(sig: ListSig) -> Self {
        let mut d = Self::none();
        d.lists.push(Conj::pos_of(sig));
        d
    }

    pub(super) fn list_of(cx: TyCtx<'_>, elem: Ty) -> Self {
        Self::list_sig(ListSig::possibly_empty(&cx, elem))
    }

    pub(super) fn non_empty_list_of(cx: TyCtx<'_>, elem: Ty) -> Self {
        let mut d = Self::none();
        if let Some(sig) = ListSig::non_empty(&cx, elem) {
            d.lists.push(Conj::pos_of(sig));
        }
        d
    }

    pub(super) fn empty_list() -> Self {
        Self::list_sig(ListSig::empty())
    }

    pub(super) fn arrow(args: impl IntoIterator<Item = Ty>, ret: Ty) -> Self {
        let mut d = Self::none();
        d.funcs.push(Conj::pos_of(ArrowSig {
            args: args.into_iter().collect(),
            ret,
            lit: None,
        }));
        d
    }

    pub(super) fn map_top() -> Self {
        let mut d = Self::none();
        d.maps.push(Conj::top());
        d
    }

    pub(super) fn map_of(fields: impl IntoIterator<Item = (MapKey, Ty)>) -> Self {
        let mut d = Self::none();
        d.maps.push(Conj::pos_of(MapSig {
            fields: fields.into_iter().collect(),
        }));
        d
    }

    pub(super) fn as_atom_singleton(&self) -> Option<&str> {
        (!self.atoms.cofinite && self.atoms.set.len() == 1)
            .then(|| self.atoms.set.iter().next().map(String::as_str))
            .flatten()
    }

    pub(super) fn atom_literals(&self) -> Option<Vec<String>> {
        (!self.atoms.cofinite).then(|| self.atoms.set.iter().cloned().collect())
    }

    pub(super) fn as_opaque_singleton(&self) -> Option<&str> {
        (!self.opaques.cofinite && self.opaques.set.len() == 1)
            .then(|| self.opaques.set.iter().next().map(String::as_str))
            .flatten()
    }

    #[cfg(test)]
    pub(super) fn as_brand_singleton(&self) -> Option<&str> {
        (!self.brands.cofinite && self.brands.set.len() == 1)
            .then(|| self.brands.set.iter().next().map(String::as_str))
            .flatten()
    }

    #[cfg(test)]
    pub(super) fn as_tuple_singleton(&self) -> Option<&[Ty]> {
        if self.basic.is_empty()
            && self.atoms.is_none()
            && self.opaques.is_none()
            && self.brands.is_none()
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

    pub(super) fn kinds_overlap(&self, other: &Descr) -> bool {
        (!self.basic.intersect(other.basic).is_empty())
            || (!self.atoms.is_none() && !other.atoms.is_none())
            || (!self.opaques.is_none() && !other.opaques.is_none())
            || (!self.brands.is_none() && !other.brands.is_none())
            || (!self.vars.is_none() && !other.vars.is_none())
            || (!self.tuples.is_empty() && !other.tuples.is_empty())
            || (!self.lists.is_empty() && !other.lists.is_empty())
            || (!self.resources.is_empty() && !other.resources.is_empty())
            || (!self.funcs.is_empty() && !other.funcs.is_empty())
            || (!self.maps.is_empty() && !other.maps.is_empty())
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

    pub(super) fn without_closure_lits(mut self) -> Descr {
        for conj in &mut self.funcs {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                sig.lit = None;
            }
        }
        self
    }

    pub(super) fn as_pure_list(&self, _cx: TyCtx<'_>) -> Option<&ListSig> {
        self.axis_free()
            .then_some(())
            .and_then(|_| single_positive(&self.lists))
            .filter(|_| {
                self.tuples.is_empty() && self.resources.is_empty() && self.funcs.is_empty() && self.maps.is_empty()
            })
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
            && self.brands.is_none()
            && self.vars.is_none()
    }

    pub(super) fn looks_empty(&self) -> bool {
        self.axis_free()
            && self.tuples.is_empty()
            && self.lists.is_empty()
            && self.resources.is_empty()
            && self.funcs.is_empty()
            && self.maps.is_empty()
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

    pub(super) fn union(&self, _cx: TyCtx<'_>, other: &Descr) -> Descr {
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

    pub(super) fn neg(&self) -> Descr {
        Descr {
            basic: self.basic.neg(),
            atoms: self.atoms.neg(),
            opaques: self.opaques.neg(),
            brands: self.brands.neg(),
            vars: self.vars.neg(),
            tuples: dnf_neg(&self.tuples),
            lists: dnf_neg(&self.lists),
            resources: dnf_neg(&self.resources),
            funcs: dnf_neg(&self.funcs),
            maps: dnf_neg(&self.maps),
        }
    }

    pub(super) fn diff(&self, other: &Descr) -> Descr {
        self.intersect(&other.neg())
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
        let result = self.basic.is_empty()
            && self.atoms.is_none()
            && self.opaques.is_none()
            && self.brands.is_none()
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
        let mut d = self.clone();
        let brands = std::mem::replace(&mut d.brands, LiteralSet::none());
        let opaques = std::mem::replace(&mut d.opaques, LiteralSet::none());
        // Finite brands: mint_brand embeds the inner's structural axes directly in the
        // descriptor (replacing the inner's own brand axis), so clearing suffices.
        // Cofinite brands (e.g. from any()): we cannot enumerate inners; widen to any.
        if brands.cofinite {
            d = d.union(cx, &Descr::any());
        }
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
