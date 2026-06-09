//! Interned set-theoretic type implementation.
//!
//! This module intentionally duplicates the concrete type kernel instead of
//! depending on `concrete_types::Descr`. Its `Descr` is private here, and every
//! structural child is a `Ty` allocated by the owning
//! `Types` instance.

mod bits;
mod conj;
mod descr;
mod dnf;
mod emptiness;
mod format;
mod lit_set;
mod sigs;

use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};

use crate::runtime_type_predicate::{ListShape, ObservedSet, RuntimeTypePredicate};
use crate::type_expr::opaque_owner_module;
use crate::types::{
    ClosureTypes as SharedClosureTypes, RenderTypes as SharedRenderTypes, Types as SharedTypes,
    VisibilityTypes as SharedVisibilityTypes,
};

pub use crate::types::{
    CallableClause, CallableValueKind, ClosureLitInfo, ClosureTarget, MapKey, Nominals, OpaqueVisibilityError, Sigma,
    TypeVarId,
};

use conj::Conj;
use descr::Descr;
use lit_set::{LiteralSet, closure_ret_var_id, closure_var_id};
use sigs::{ArrowSig, ClosureLit, ListSig, MergeSig};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Ty(u32);

#[derive(Default)]
pub struct Types {
    interner: TypeInterner,
    comparisons: RefCell<ComparisonCache>,
}

#[derive(Default)]
struct TypeInterner {
    arena: Vec<Descr>,
    index: HashMap<Descr, Ty>,
}

#[derive(Default)]
struct ComparisonCache {
    values: HashMap<ComparisonKey, bool>,
    hits: usize,
    misses: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ComparisonKey {
    Empty(Ty),
    Subtype(Ty, Ty),
    Disjoint(Ty, Ty),
    Equivalent(Ty, Ty),
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ComparisonCacheStats {
    pub entries: usize,
    pub hits: usize,
    pub misses: usize,
}

#[derive(Clone, Copy)]
pub(super) struct TyCtx<'a> {
    arena: &'a [Descr],
}

impl<'a> TyCtx<'a> {
    fn descr(&self, t: &Ty) -> &'a Descr {
        self.arena
            .get(t.0 as usize)
            .unwrap_or_else(|| panic!("unknown interned type id {}", t.0))
    }
}

impl TypeInterner {
    fn intern(&mut self, d: Descr) -> Ty {
        if let Some(ty) = self.index.get(&d) {
            return *ty;
        }
        let raw = self.arena.len();
        assert!(u32::try_from(raw).is_ok(), "type interner exhausted ids");
        let ty = Ty(raw as u32);
        self.arena.push(d.clone());
        self.index.insert(d, ty);
        ty
    }

    fn ctx(&self) -> TyCtx<'_> {
        TyCtx { arena: &self.arena }
    }

    fn descr(&self, t: &Ty) -> &Descr {
        self.ctx().descr(t)
    }
}

impl Types {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn repeat(&mut self, ty: Ty, n: usize) -> Vec<Ty> {
        vec![ty; n]
    }

    pub fn bool_lit(&mut self, value: bool) -> Ty {
        self.atom_lit(if value { "true" } else { "false" })
    }

    pub fn cpointer(&mut self) -> Ty {
        self.opaque_of("cpointer")
    }

    pub fn differs_only_nominally(&self, a: &Ty, b: &Ty) -> bool {
        self.is_disjoint(a, b) && !self.is_value_disjoint(a, b)
    }

    pub fn key_is_strictly_more_specific(&self, lhs: &[Ty], rhs: &[Ty]) -> bool {
        lhs.len() == rhs.len()
            && lhs
                .iter()
                .zip(rhs.iter())
                .fold((true, false), |(all_le, any_strict), (l, r)| {
                    (all_le && self.is_subtype(l, r), any_strict || !self.is_subtype(r, l))
                })
                == (true, true)
    }

    pub fn as_map_key(&self, a: &Ty) -> Option<MapKey> {
        self.as_int_singleton(a)
            .map(MapKey::Int)
            .or_else(|| self.as_atom_singleton(a).map(MapKey::Atom))
    }

    fn intern(&mut self, d: Descr) -> Ty {
        self.interner.intern(d)
    }

    fn ctx(&self) -> TyCtx<'_> {
        self.interner.ctx()
    }

    fn descr(&self, t: &Ty) -> &Descr {
        self.interner.descr(t)
    }

    fn cached_comparison(&self, key: ComparisonKey, compute: impl FnOnce(&Self) -> bool) -> bool {
        if let Some(result) = self.comparisons.borrow_mut().hit(key) {
            return result;
        }
        let result = compute(self);
        self.comparisons.borrow_mut().miss(key, result);
        result
    }

    fn symmetric_key(kind: fn(Ty, Ty) -> ComparisonKey, a: Ty, b: Ty) -> ComparisonKey {
        if a <= b { kind(a, b) } else { kind(b, a) }
    }

    #[cfg(test)]
    pub(crate) fn comparison_cache_stats(&self) -> ComparisonCacheStats {
        let cache = self.comparisons.borrow();
        ComparisonCacheStats {
            entries: cache.values.len(),
            hits: cache.hits,
            misses: cache.misses,
        }
    }
}

impl ComparisonCache {
    fn hit(&mut self, key: ComparisonKey) -> Option<bool> {
        let result = self.values.get(&key).copied();
        if result.is_some() {
            self.hits += 1;
        }
        result
    }

    fn miss(&mut self, key: ComparisonKey, result: bool) {
        self.misses += 1;
        self.values.insert(key, result);
    }
}

impl Types {
    pub fn any(&mut self) -> Ty {
        self.intern(Descr::any())
    }

    pub fn none(&mut self) -> Ty {
        self.intern(Descr::none())
    }

    pub fn nil(&mut self) -> Ty {
        self.intern(Descr::nil())
    }

    pub fn bool(&mut self) -> Ty {
        self.intern(Descr::bool_t())
    }

    pub fn int(&mut self) -> Ty {
        self.intern(Descr::int())
    }

    pub fn int_lit(&mut self, n: i64) -> Ty {
        self.intern(Descr::int_lit(n))
    }

    pub fn float(&mut self) -> Ty {
        self.intern(Descr::float())
    }

    pub fn float_lit(&mut self, f: f64) -> Ty {
        self.intern(Descr::float_lit(f))
    }

    pub fn atom(&mut self) -> Ty {
        self.intern(Descr::atom_top())
    }

    pub fn atom_lit(&mut self, name: &str) -> Ty {
        self.intern(Descr::atom_lit(name))
    }

    pub fn type_var(&mut self, id: TypeVarId) -> Ty {
        self.intern(Descr::var(id))
    }

    pub fn resource(&mut self, payload: Ty) -> Ty {
        self.intern(Descr::resource_of(self.ctx(), payload))
    }

    pub fn arrow(&mut self, args: &[Ty], ret: Ty) -> Ty {
        self.intern(Descr::arrow(args.iter().copied(), ret))
    }

    pub fn tuple(&mut self, elems: &[Ty]) -> Ty {
        self.intern(Descr::tuple_of(elems.iter().copied()))
    }

    pub fn empty_list(&mut self) -> Ty {
        self.intern(Descr::empty_list())
    }

    pub fn list(&mut self, elem: Ty) -> Ty {
        self.intern(Descr::list_of(self.ctx(), elem))
    }

    pub fn non_empty_list(&mut self, elem: Ty) -> Ty {
        self.intern(Descr::non_empty_list_of(self.ctx(), elem))
    }

    pub fn map(&mut self, fields: &[(MapKey, Ty)]) -> Ty {
        self.intern(Descr::map_of(fields.iter().cloned()))
    }

    pub fn str_t(&mut self) -> Ty {
        self.intern(Descr::str_t())
    }

    pub fn map_top(&mut self) -> Ty {
        self.intern(Descr::map_top())
    }

    pub fn mint_brand(&mut self, inner: Ty, name: &str) -> Ty {
        let mut d = self.descr(&inner).clone();
        d.brands = LiteralSet::lit(name.to_string());
        self.intern(d)
    }

    pub fn opaque_of(&mut self, name: &str) -> Ty {
        self.intern(Descr::opaque_of(name))
    }

    pub fn brand_of(&mut self, name: &str) -> Ty {
        self.intern(Descr::brand_of(name))
    }

    pub fn list_element_type(&mut self, a: &Ty) -> Ty {
        let d = {
            let cx = self.ctx();
            list_element_type(cx, cx.descr(a))
        };
        self.intern(d)
    }

    pub fn has_list_shape(&self, a: &Ty) -> bool {
        !self.descr(a).lists.is_empty()
    }

    pub fn resource_payload_type(&mut self, a: &Ty) -> Option<Ty> {
        let d = {
            let cx = self.ctx();
            resource_payload_type(cx, cx.descr(a))?
        };
        Some(self.intern(d))
    }

    pub fn mint_owned_resource_aliases(&mut self, a: Ty, owner: &str, opaque_inners: &HashMap<String, Ty>) -> Ty {
        let candidates = opaque_inners
            .iter()
            .filter_map(|(tag, inner)| {
                let tag_owner = opaque_owner_module(tag)?;
                (tag_owner == owner).then(|| (tag.clone(), self.descr(inner).clone()))
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return a;
        }
        let d = mint_owned_resource_aliases_descr(self.ctx(), self.descr(&a), &candidates);
        self.intern(d)
    }

    pub fn tuple_projections(&mut self, a: &Ty, arity: usize) -> Vec<Ty> {
        let ds = {
            let cx = self.ctx();
            tuple_projections(cx, cx.descr(a), arity)
        };
        ds.into_iter().map(|d| self.intern(d)).collect()
    }

    pub fn tuple_field_type(&mut self, a: &Ty, index: usize) -> Ty {
        let d = {
            let cx = self.ctx();
            tuple_field_type(cx, cx.descr(a), index)
        };
        self.intern(d)
    }

    pub fn max_tuple_arity(&self, a: &Ty) -> usize {
        self.descr(a).max_tuple_arity()
    }

    pub fn refine_map_field(&mut self, a: &Ty, key: &MapKey, v: &Ty) -> Ty {
        let d = self.descr(a).refine_map_field(key, *v);
        self.intern(d)
    }

    pub fn map_field_lookup(&mut self, a: &Ty, key: &MapKey) -> Option<Ty> {
        let d = {
            let cx = self.ctx();
            map_field_lookup(cx, cx.descr(a), key)?
        };
        Some(self.intern(d))
    }

    pub fn map_known_keys(&self, a: &Ty) -> Vec<MapKey> {
        map_known_keys(self.descr(a))
    }

    pub fn widen_for_recursive_spec_key(&mut self, a: &Ty) -> Ty {
        let d = widen_for_recursive_spec_key(self, *a);
        self.intern(d)
    }

    pub fn alpha_normalize_vars(&mut self, a: &Ty) -> Ty {
        let d = alpha_normalize_vars(self, *a);
        self.intern(d)
    }

    pub fn refine_widen(&mut self, a: &Ty, b: &Ty) -> Ty {
        let d = refine_widen(self, *a, *b);
        self.intern(d)
    }

    pub fn convergence_class(&mut self, a: &Ty) -> Ty {
        if as_pure_list(self.ctx(), self.descr(a)).is_some() {
            let any = self.any();
            self.list(any)
        } else {
            *a
        }
    }

    pub fn union(&mut self, a: Ty, b: Ty) -> Ty {
        let d = {
            let cx = self.ctx();
            cx.descr(&a).union(cx, cx.descr(&b))
        };
        self.intern(d)
    }

    pub fn intersect(&mut self, a: Ty, b: Ty) -> Ty {
        if a == b {
            return a;
        }
        if self.is_subtype(&a, &b) {
            return a;
        }
        if self.is_subtype(&b, &a) {
            return b;
        }
        let left = self.descr(&a).clone();
        let right = self.descr(&b).clone();
        let d = intersect_descr(self, &left, &right);
        self.intern(d)
    }

    #[cfg(test)]
    pub fn complement(&mut self, a: Ty) -> Ty {
        let d = self.descr(&a).neg();
        self.intern(d)
    }

    pub fn difference(&mut self, a: Ty, b: Ty) -> Ty {
        let d = self.descr(&a).diff(self.descr(&b));
        self.intern(d)
    }

    pub fn is_empty(&self, a: &Ty) -> bool {
        self.cached_comparison(ComparisonKey::Empty(*a), |types| {
            let cx = types.ctx();
            types.descr(a).is_empty(cx)
        })
    }

    #[cfg(test)]
    pub fn is_top(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_equiv(cx, &Descr::any())
    }

    pub fn is_subtype(&self, a: &Ty, b: &Ty) -> bool {
        if a == b {
            return true;
        }
        self.cached_comparison(ComparisonKey::Subtype(*a, *b), |types| {
            let cx = types.ctx();
            types.descr(a).is_subtype(cx, types.descr(b))
        })
    }

    pub fn is_disjoint(&self, a: &Ty, b: &Ty) -> bool {
        if a == b {
            return self.is_empty(a);
        }
        let key = Self::symmetric_key(ComparisonKey::Disjoint, *a, *b);
        self.cached_comparison(key, |types| {
            let cx = types.ctx();
            types.descr(a).intersect(types.descr(b)).is_empty(cx)
        })
    }

    pub fn is_value_disjoint(&self, a: &Ty, b: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).value_disjoint(cx, self.descr(b))
    }

    pub fn key_var_count(&self, key: &[Ty]) -> usize {
        key.iter().map(|t| self.descr(t).vars.finite_len().unwrap_or(0)).sum()
    }

    pub fn key_subsumes_with(&self, query: &Ty, key: &Ty, sigma: &mut Sigma<Ty>) -> bool {
        let qd = self.descr(query);
        let kd = self.descr(key);
        if kd.looks_full() {
            return true;
        }
        if let Some(alphas) = pure_var_ids(kd) {
            for alpha in alphas {
                match sigma.get(&alpha) {
                    None => {
                        sigma.insert(alpha, *query);
                    }
                    Some(existing) => {
                        let cx = self.ctx();
                        if !self.descr(existing).is_equiv(cx, qd) {
                            return false;
                        }
                    }
                }
            }
            return true;
        }
        let cx = self.ctx();
        qd.is_subtype(cx, kd)
    }

    pub fn is_equivalent(&self, a: &Ty, b: &Ty) -> bool {
        if a == b {
            return true;
        }
        let key = Self::symmetric_key(ComparisonKey::Equivalent, *a, *b);
        self.cached_comparison(key, |types| types.is_subtype(a, b) && types.is_subtype(b, a))
    }

    pub fn kinds_overlap(&self, a: &Ty, b: &Ty) -> bool {
        self.descr(a).kinds_overlap(self.descr(b))
    }

    pub fn opaque_singleton(&self, a: &Ty) -> Option<String> {
        self.descr(a).as_opaque_singleton().map(String::from)
    }

    #[cfg(test)]
    pub fn brand_singleton(&self, a: &Ty) -> Option<String> {
        self.descr(a).as_brand_singleton().map(String::from)
    }

    pub fn is_singleton_lit(&self, a: &Ty) -> bool {
        self.descr(a).is_singleton_literal()
    }

    pub fn as_int_singleton(&self, a: &Ty) -> Option<i64> {
        self.descr(a).as_int_singleton()
    }

    pub fn as_float_singleton(&self, a: &Ty) -> Option<f64> {
        self.descr(a).as_float_singleton().map(|b| b.get())
    }

    pub fn as_atom_singleton(&self, a: &Ty) -> Option<String> {
        self.descr(a).as_atom_singleton().map(String::from)
    }

    pub(crate) fn runtime_type_predicate(&self, a: &Ty) -> RuntimeTypePredicate {
        let descr = self.descr(a);
        if runtime_type_predicate_requires_any(descr) {
            return RuntimeTypePredicate::any();
        }
        RuntimeTypePredicate {
            ints: ObservedSet {
                cofinite: descr.ints.cofinite,
                values: descr.ints.set.iter().copied().collect(),
            },
            floats: ObservedSet {
                cofinite: descr.floats.cofinite,
                values: descr.floats.set.iter().map(|bits| bits.get().to_bits()).collect(),
            },
            atoms: ObservedSet {
                cofinite: descr.atoms.cofinite,
                values: descr.atoms.set.iter().cloned().collect(),
            },
            lists: runtime_type_predicate_list_shapes(descr),
            tuple_arities: runtime_type_predicate_tuple_arities(descr),
            named_structs: runtime_type_predicate_named_structs(descr),
            allow_other_structs: false,
            maps: !descr.maps.is_empty(),
            binaries: !descr.basic.is_empty(),
            closures: !descr.funcs.is_empty(),
            resources: !descr.resources.is_empty(),
        }
    }

    pub(crate) fn atom_literals(&self, a: &Ty) -> Vec<String> {
        self.descr(a).atom_literals().unwrap_or_default()
    }

    pub fn arrow_join_return(&mut self, a: &Ty) -> Ty {
        let d = {
            let cx = self.ctx();
            arrow_join_return(cx, cx.descr(a))
        };
        self.intern(d)
    }

    #[cfg(test)]
    pub fn tuple_lit_elems(&self, a: &Ty) -> Option<Vec<Ty>> {
        tuple_lit_elems(self.ctx(), self.descr(a))
    }

    pub fn is_integer(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::int())
    }

    pub fn is_floating(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::float())
    }

    pub fn is_nil(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::nil())
    }

    #[cfg(test)]
    pub fn is_bool(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::bool_t())
    }

    #[cfg(test)]
    pub fn is_atom_type(&self, a: &Ty) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::atom_top())
    }

    pub fn has_vars(&self, a: &Ty) -> bool {
        has_vars(self.ctx(), self.descr(a))
    }

    pub fn instantiate(&mut self, a: &Ty, sigma: &Sigma<Ty>) -> Ty {
        let d = instantiate(self, *a, sigma);
        self.intern(d)
    }

    pub fn collect_instantiation_subst(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) {
        collect_subst_into(self, *pattern, *witness, sigma);
    }
}

impl Types {
    pub fn fn_ref_lit(&mut self, target: ClosureTarget, n_args: usize) -> Ty {
        let fn_id = target.into();
        let args: Vec<Ty> = (0..n_args)
            .map(|pos| self.intern(Descr::var(closure_var_id(fn_id, pos))))
            .collect();
        let ret = self.intern(Descr::var(closure_ret_var_id(fn_id)));
        self.intern(Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args,
                ret,
                lit: Some(ClosureLit {
                    kind: CallableValueKind::FnRef,
                    fn_id,
                    captures: Vec::new(),
                }),
            })],
            ..Descr::none()
        })
    }

    pub fn closure_lit(&mut self, target: ClosureTarget, captures: Vec<Ty>, n_args: usize) -> Ty {
        let fn_id = target.into();
        let args: Vec<Ty> = (0..n_args)
            .map(|pos| self.intern(Descr::var(closure_var_id(fn_id, pos))))
            .collect();
        let ret = self.intern(Descr::var(closure_ret_var_id(fn_id)));
        self.intern(Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args,
                ret,
                lit: Some(ClosureLit {
                    kind: CallableValueKind::Closure,
                    fn_id,
                    captures,
                }),
            })],
            ..Descr::none()
        })
    }

    pub fn closure_lit_parts(&self, a: &Ty) -> Option<ClosureLitInfo<Ty>> {
        let lit = self.descr(a).as_closure_lit()?;
        Some(ClosureLitInfo {
            target: lit.fn_id.into(),
            captures: lit.captures.clone(),
            kind: lit.kind,
        })
    }

    pub fn callable_clauses(&mut self, a: &Ty) -> Option<Vec<CallableClause<Ty>>> {
        callable_clauses(self.ctx(), self.descr(a))
    }

    pub fn callable_value_clauses(&mut self, a: &Ty) -> Option<Vec<CallableClause<Ty>>> {
        let clauses = self.callable_clauses(a)?;
        let surface_clauses = clauses
            .iter()
            .filter(|clause| clause.closure.is_none())
            .cloned()
            .collect::<Vec<_>>();
        if surface_clauses.is_empty() {
            return Some(clauses);
        }

        let mut resolved = Vec::new();
        for clause in clauses {
            if clause.closure.is_none() {
                continue;
            }
            let mut specialized = false;
            for surface in surface_clauses
                .iter()
                .filter(|surface| surface.args.len() == clause.args.len())
            {
                specialized = true;
                let resolved_clause = specialize_callable_clause(self, &clause, surface);
                if !resolved.contains(&resolved_clause) {
                    resolved.push(resolved_clause);
                }
            }
            if !specialized && !resolved.contains(&clause) {
                resolved.push(clause);
            }
        }

        if resolved.is_empty() {
            Some(surface_clauses)
        } else {
            Some(resolved)
        }
    }

    pub fn erase_closure_identity(&mut self, a: &Ty) -> Ty {
        let d = erase_closure_identity(self, *a);
        self.intern(d)
    }
}

impl Types {
    pub fn check_opaque_visibility(&self, a: &Ty, using_module: &str) -> Result<(), OpaqueVisibilityError> {
        let Some(tag) = self.descr(a).as_opaque_singleton() else {
            return Ok(());
        };
        let Some(owner) = opaque_owner_module(tag) else {
            return Ok(());
        };
        if owner == using_module {
            Ok(())
        } else {
            Err(OpaqueVisibilityError {
                opaque: tag.to_string(),
                owner_module: owner.to_string(),
                using_module: using_module.to_string(),
            })
        }
    }
}

impl Types {
    pub fn display(&self, a: &Ty) -> String {
        format::display(self.ctx(), self.descr(a))
    }

    pub fn display_for_diag(&self, a: &Ty) -> String {
        format::display_for_diag(self.ctx(), self.descr(a))
    }
}

impl SharedTypes for Types {
    type Ty = Ty;

    fn any(&mut self) -> Self::Ty {
        Types::any(self)
    }

    fn none(&mut self) -> Self::Ty {
        Types::none(self)
    }

    fn nil(&mut self) -> Self::Ty {
        Types::nil(self)
    }

    fn bool(&mut self) -> Self::Ty {
        Types::bool(self)
    }

    fn int(&mut self) -> Self::Ty {
        Types::int(self)
    }

    fn int_lit(&mut self, n: i64) -> Self::Ty {
        Types::int_lit(self, n)
    }

    fn float(&mut self) -> Self::Ty {
        Types::float(self)
    }

    fn float_lit(&mut self, f: f64) -> Self::Ty {
        Types::float_lit(self, f)
    }

    fn atom(&mut self) -> Self::Ty {
        Types::atom(self)
    }

    fn atom_lit(&mut self, name: &str) -> Self::Ty {
        Types::atom_lit(self, name)
    }

    fn type_var(&mut self, id: TypeVarId) -> Self::Ty {
        Types::type_var(self, id)
    }

    fn resource(&mut self, payload: Self::Ty) -> Self::Ty {
        Types::resource(self, payload)
    }

    fn arrow(&mut self, args: &[Self::Ty], ret: Self::Ty) -> Self::Ty {
        Types::arrow(self, args, ret)
    }

    fn tuple(&mut self, elems: &[Self::Ty]) -> Self::Ty {
        Types::tuple(self, elems)
    }

    fn empty_list(&mut self) -> Self::Ty {
        Types::empty_list(self)
    }

    fn list(&mut self, elem: Self::Ty) -> Self::Ty {
        Types::list(self, elem)
    }

    fn non_empty_list(&mut self, elem: Self::Ty) -> Self::Ty {
        Types::non_empty_list(self, elem)
    }

    fn map(&mut self, fields: &[(MapKey, Self::Ty)]) -> Self::Ty {
        Types::map(self, fields)
    }

    fn str_t(&mut self) -> Self::Ty {
        Types::str_t(self)
    }

    fn map_top(&mut self) -> Self::Ty {
        Types::map_top(self)
    }

    fn mint_brand(&mut self, inner: Self::Ty, name: &str) -> Self::Ty {
        Types::mint_brand(self, inner, name)
    }

    fn opaque_of(&mut self, name: &str) -> Self::Ty {
        Types::opaque_of(self, name)
    }

    fn brand_of(&mut self, name: &str) -> Self::Ty {
        Types::brand_of(self, name)
    }

    fn list_element_type(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::list_element_type(self, a)
    }

    fn has_list_shape(&self, a: &Self::Ty) -> bool {
        Types::has_list_shape(self, a)
    }

    fn resource_payload_type(&mut self, a: &Self::Ty) -> Option<Self::Ty> {
        Types::resource_payload_type(self, a)
    }

    fn mint_owned_resource_aliases(
        &mut self,
        a: Self::Ty,
        owner: &str,
        opaque_inners: &HashMap<String, Self::Ty>,
    ) -> Self::Ty {
        Types::mint_owned_resource_aliases(self, a, owner, opaque_inners)
    }

    fn tuple_projections(&mut self, a: &Self::Ty, arity: usize) -> Vec<Self::Ty> {
        Types::tuple_projections(self, a, arity)
    }

    fn tuple_field_type(&mut self, a: &Self::Ty, index: usize) -> Self::Ty {
        Types::tuple_field_type(self, a, index)
    }

    fn max_tuple_arity(&self, a: &Self::Ty) -> usize {
        Types::max_tuple_arity(self, a)
    }

    fn refine_map_field(&mut self, a: &Self::Ty, key: &MapKey, v: &Self::Ty) -> Self::Ty {
        Types::refine_map_field(self, a, key, v)
    }

    fn map_field_lookup(&mut self, a: &Self::Ty, key: &MapKey) -> Option<Self::Ty> {
        Types::map_field_lookup(self, a, key)
    }

    fn map_known_keys(&self, a: &Self::Ty) -> Vec<MapKey> {
        Types::map_known_keys(self, a)
    }

    fn widen_for_recursive_spec_key(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::widen_for_recursive_spec_key(self, a)
    }

    fn alpha_normalize_vars(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::alpha_normalize_vars(self, a)
    }

    fn refine_widen(&mut self, a: &Self::Ty, b: &Self::Ty) -> Self::Ty {
        Types::refine_widen(self, a, b)
    }

    fn convergence_class(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::convergence_class(self, a)
    }

    fn union(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty {
        Types::union(self, a, b)
    }

    fn intersect(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty {
        Types::intersect(self, a, b)
    }

    #[cfg(test)]
    fn complement(&mut self, a: Self::Ty) -> Self::Ty {
        Types::complement(self, a)
    }

    fn difference(&mut self, a: Self::Ty, b: Self::Ty) -> Self::Ty {
        Types::difference(self, a, b)
    }

    fn is_empty(&self, a: &Self::Ty) -> bool {
        Types::is_empty(self, a)
    }

    #[cfg(test)]
    fn is_top(&self, a: &Self::Ty) -> bool {
        Types::is_top(self, a)
    }

    fn is_subtype(&self, a: &Self::Ty, b: &Self::Ty) -> bool {
        Types::is_subtype(self, a, b)
    }

    fn is_disjoint(&self, a: &Self::Ty, b: &Self::Ty) -> bool {
        Types::is_disjoint(self, a, b)
    }

    fn is_value_disjoint(&self, a: &Self::Ty, b: &Self::Ty, _nominals: Nominals<'_, Self::Ty>) -> bool {
        Types::is_value_disjoint(self, a, b)
    }

    fn key_var_count(&self, key: &[Self::Ty]) -> usize {
        Types::key_var_count(self, key)
    }

    fn key_subsumes_with(&self, query: &Self::Ty, key: &Self::Ty, sigma: &mut Sigma<Self::Ty>) -> bool {
        Types::key_subsumes_with(self, query, key, sigma)
    }

    fn kinds_overlap(&self, a: &Self::Ty, b: &Self::Ty) -> bool {
        Types::kinds_overlap(self, a, b)
    }

    fn opaque_singleton(&self, a: &Self::Ty) -> Option<String> {
        Types::opaque_singleton(self, a)
    }

    #[cfg(test)]
    fn brand_singleton(&self, a: &Self::Ty) -> Option<String> {
        Types::brand_singleton(self, a)
    }

    fn is_singleton_lit(&self, a: &Self::Ty) -> bool {
        Types::is_singleton_lit(self, a)
    }

    fn as_int_singleton(&self, a: &Self::Ty) -> Option<i64> {
        Types::as_int_singleton(self, a)
    }

    fn as_float_singleton(&self, a: &Self::Ty) -> Option<f64> {
        Types::as_float_singleton(self, a)
    }

    fn as_atom_singleton(&self, a: &Self::Ty) -> Option<String> {
        Types::as_atom_singleton(self, a)
    }

    fn arrow_join_return(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::arrow_join_return(self, a)
    }

    #[cfg(test)]
    fn tuple_lit_elems(&self, a: &Self::Ty) -> Option<Vec<Self::Ty>> {
        Types::tuple_lit_elems(self, a)
    }

    fn instantiate(&mut self, a: &Self::Ty, sigma: &Sigma<Self::Ty>) -> Self::Ty {
        Types::instantiate(self, a, sigma)
    }

    fn collect_instantiation_subst(&mut self, pattern: &Self::Ty, witness: &Self::Ty, sigma: &mut Sigma<Self::Ty>) {
        Types::collect_instantiation_subst(self, pattern, witness, sigma)
    }

    fn is_integer(&self, a: &Self::Ty) -> bool {
        Types::is_integer(self, a)
    }

    fn is_floating(&self, a: &Self::Ty) -> bool {
        Types::is_floating(self, a)
    }

    fn is_nil(&self, a: &Self::Ty) -> bool {
        Types::is_nil(self, a)
    }

    #[cfg(test)]
    fn is_bool(&self, a: &Self::Ty) -> bool {
        Types::is_bool(self, a)
    }

    #[cfg(test)]
    fn is_atom_type(&self, a: &Self::Ty) -> bool {
        Types::is_atom_type(self, a)
    }

    fn has_vars(&self, a: &Self::Ty) -> bool {
        Types::has_vars(self, a)
    }
}

impl SharedClosureTypes for Types {
    fn fn_ref_lit(&mut self, target: ClosureTarget, n_args: usize) -> Self::Ty {
        Types::fn_ref_lit(self, target, n_args)
    }

    fn closure_lit(&mut self, target: ClosureTarget, captures: Vec<Self::Ty>, n_args: usize) -> Self::Ty {
        Types::closure_lit(self, target, captures, n_args)
    }

    fn closure_lit_parts(&self, a: &Self::Ty) -> Option<ClosureLitInfo<Self::Ty>> {
        Types::closure_lit_parts(self, a)
    }

    fn callable_clauses(&mut self, a: &Self::Ty) -> Option<Vec<CallableClause<Self::Ty>>> {
        Types::callable_clauses(self, a)
    }

    fn erase_closure_identity(&mut self, a: &Self::Ty) -> Self::Ty {
        Types::erase_closure_identity(self, a)
    }
}

impl SharedVisibilityTypes for Types {
    fn check_opaque_visibility(&self, a: &Self::Ty, using_module: &str) -> Result<(), OpaqueVisibilityError> {
        Types::check_opaque_visibility(self, a, using_module)
    }
}

impl SharedRenderTypes for Types {
    fn display(&self, a: &Self::Ty) -> String {
        Types::display(self, a)
    }

    fn display_for_diag(&self, a: &Self::Ty) -> String {
        Types::display_for_diag(self, a)
    }
}

fn pure_var_ids(d: &Descr) -> Option<Vec<TypeVarId>> {
    let finite: Vec<TypeVarId> = d.vars.finite()?.collect();
    let only_vars = d.basic.is_empty()
        && d.atoms.is_none()
        && d.ints.is_none()
        && d.floats.is_none()
        && d.opaques.is_none()
        && d.brands.is_none()
        && d.tuples.is_empty()
        && d.lists.is_empty()
        && d.resources.is_empty()
        && d.funcs.is_empty()
        && d.maps.is_empty();
    (only_vars && !finite.is_empty()).then_some(finite)
}

fn intersect_descr(types: &mut Types, a: &Descr, b: &Descr) -> Descr {
    Descr {
        basic: a.basic.intersect(b.basic),
        atoms: a.atoms.intersect(&b.atoms),
        ints: a.ints.intersect(&b.ints),
        floats: a.floats.intersect(&b.floats),
        opaques: a.opaques.intersect(&b.opaques),
        brands: a.brands.intersect(&b.brands),
        vars: a.vars.intersect(&b.vars),
        tuples: intersect_dnf(types, &a.tuples, &b.tuples),
        lists: intersect_dnf(types, &a.lists, &b.lists),
        resources: intersect_dnf(types, &a.resources, &b.resources),
        funcs: intersect_dnf(types, &a.funcs, &b.funcs),
        maps: intersect_dnf(types, &a.maps, &b.maps),
    }
}

fn intersect_dnf<T: MergeSig>(types: &mut Types, a: &[Conj<T>], b: &[Conj<T>]) -> Vec<Conj<T>> {
    let mut out = Vec::with_capacity(a.len() * b.len());
    for c1 in a {
        for c2 in b {
            out.push(intersect_clauses(types, c1, c2));
        }
    }
    out
}

fn intersect_clauses<T: MergeSig>(types: &mut Types, a: &Conj<T>, b: &Conj<T>) -> Conj<T> {
    let mut pos = a.pos.clone();
    for new_sig in &b.pos {
        let mut merged = false;
        for slot in pos.iter_mut() {
            if let Some(narrowed) = T::intersect_pos(types, slot, new_sig) {
                *slot = narrowed;
                merged = true;
                break;
            }
        }
        if !merged && !pos.contains(new_sig) {
            pos.push(new_sig.clone());
        }
    }
    let mut neg = a.neg.clone();
    for sig in &b.neg {
        if !neg.contains(sig) {
            neg.push(sig.clone());
        }
    }
    Conj { pos, neg }
}

fn list_element_type(cx: TyCtx<'_>, d: &Descr) -> Descr {
    if d.lists.is_empty() {
        return Descr::any();
    }
    let mut elem = Descr::none();
    let mut found = false;
    for conj in &d.lists {
        let mut clause_elem: Option<Descr> = None;
        for sig in &conj.pos {
            let Some(sig_elem) = sig.elem else {
                continue;
            };
            let sig_elem = cx.descr(&sig_elem);
            clause_elem = Some(match clause_elem {
                None => sig_elem.clone(),
                Some(prev) => prev.intersect(sig_elem),
            });
        }
        if let Some(e) = clause_elem {
            elem = elem.union(cx, &e);
            found = true;
        }
    }
    if found { elem } else { Descr::none() }
}

fn resource_payload_type(cx: TyCtx<'_>, d: &Descr) -> Option<Descr> {
    if d.resources.is_empty() {
        return None;
    }
    let mut acc = Descr::none();
    for conj in &d.resources {
        if !conj.neg.is_empty() || conj.pos.is_empty() {
            return Some(Descr::any());
        }
        let mut payload: Option<Descr> = None;
        for sig in &conj.pos {
            let sig_payload = cx.descr(&sig.payload);
            payload = Some(match payload {
                Some(prev) => prev.intersect(sig_payload),
                None => sig_payload.clone(),
            });
        }
        acc = acc.union(cx, &payload.unwrap_or_else(Descr::any));
    }
    Some(acc)
}

fn tuple_projections(cx: TyCtx<'_>, d: &Descr, arity: usize) -> Vec<Descr> {
    let mut comps = vec![Descr::none(); arity];
    let mut found = false;
    for conj in &d.tuples {
        let mut clause_comps: Option<Vec<Descr>> = None;
        for sig in &conj.pos {
            if sig.elems.len() != arity {
                continue;
            }
            clause_comps = Some(match clause_comps {
                None => sig.elems.iter().map(|t| cx.descr(t).clone()).collect(),
                Some(prev) => prev
                    .iter()
                    .zip(sig.elems.iter())
                    .map(|(p, s)| p.intersect(cx.descr(s)))
                    .collect(),
            });
        }
        if let Some(cs) = clause_comps {
            for i in 0..arity {
                comps[i] = comps[i].union(cx, &cs[i]);
            }
            found = true;
        }
    }
    if found { comps } else { vec![Descr::any(); arity] }
}

fn tuple_field_type(cx: TyCtx<'_>, d: &Descr, index: usize) -> Descr {
    let mut out = Descr::none();
    let mut found = false;
    for conj in &d.tuples {
        if conj.pos.is_empty() {
            return Descr::any();
        }

        let mut arity = None;
        let mut clause_fields: Option<Vec<Descr>> = None;
        let mut feasible = true;
        for sig in &conj.pos {
            if index >= sig.elems.len() || arity.is_some_and(|arity| arity != sig.elems.len()) {
                feasible = false;
                break;
            }
            arity = Some(sig.elems.len());
            clause_fields = Some(match clause_fields {
                None => sig.elems.iter().map(|t| cx.descr(t).clone()).collect(),
                Some(prev) => prev
                    .iter()
                    .zip(sig.elems.iter())
                    .map(|(p, s)| p.intersect(cx.descr(s)))
                    .collect(),
            });
        }
        let Some(fields) = clause_fields else {
            continue;
        };
        if !feasible || fields.iter().any(|field| field.is_empty(cx)) {
            continue;
        }
        out = out.union(cx, &fields[index]);
        found = true;
    }
    if found { out } else { Descr::none() }
}

fn map_field_lookup(cx: TyCtx<'_>, d: &Descr, key: &MapKey) -> Option<Descr> {
    if d.maps.is_empty() {
        return None;
    }
    let mut found = false;
    let mut acc = Descr::none();
    for conj in &d.maps {
        if conj.pos.is_empty() {
            acc = acc.union(cx, &Descr::any()).union(cx, &Descr::nil());
            found = true;
            continue;
        }
        let mut clause_v: Option<Descr> = None;
        for sig in &conj.pos {
            let sig_v = match sig.fields.get(key) {
                Some(t) => cx.descr(t).clone(),
                None => Descr::any().union(cx, &Descr::nil()),
            };
            clause_v = Some(match clause_v {
                None => sig_v,
                Some(prev) => prev.intersect(&sig_v),
            });
        }
        if let Some(v) = clause_v {
            acc = acc.union(cx, &v);
            found = true;
        }
    }
    if found { Some(acc) } else { None }
}

fn map_known_keys(d: &Descr) -> Vec<MapKey> {
    let mut keys = BTreeSet::new();
    for conj in &d.maps {
        for sig in &conj.pos {
            keys.extend(sig.fields.keys().cloned());
        }
    }
    keys.into_iter().collect()
}

fn callable_clauses(cx: TyCtx<'_>, d: &Descr) -> Option<Vec<CallableClause<Ty>>> {
    if d.funcs.is_empty() || d.funcs.iter().any(|c| !c.neg.is_empty() || c.pos.is_empty()) {
        return None;
    }
    Some(
        d.funcs
            .iter()
            .flat_map(|conj| conj.pos.iter())
            .map(|arrow| CallableClause {
                args: arrow.args.clone(),
                ret: arrow.ret,
                closure: arrow.lit.as_ref().map(|lit| ClosureLitInfo {
                    target: lit.fn_id.into(),
                    captures: lit.captures.clone(),
                    kind: lit.kind,
                }),
            })
            .filter(|clause| clause.args.iter().all(|arg| !cx.descr(arg).is_empty(cx)))
            .collect(),
    )
}

fn runtime_type_predicate_requires_any(descr: &Descr) -> bool {
    const STRUCT_PREFIX: &str = "impl-target::";
    descr.opaques.cofinite
        || descr.opaques.set.iter().any(|tag| !tag.starts_with(STRUCT_PREFIX))
        || descr.brands.cofinite
        || descr.vars.cofinite
        || !descr.vars.set.is_empty()
}

fn runtime_type_predicate_list_shapes(descr: &Descr) -> ObservedSet<ListShape> {
    let mut out = ObservedSet::none();
    for clause in &descr.lists {
        let mut allowed = ObservedSet::finite([ListShape::Empty, ListShape::NonEmpty]);
        for sig in &clause.pos {
            let sig_allowed = if sig.is_exact_empty() {
                ObservedSet::lit(ListShape::Empty)
            } else if sig.is_exact_non_empty() {
                ObservedSet::lit(ListShape::NonEmpty)
            } else {
                ObservedSet::finite([ListShape::Empty, ListShape::NonEmpty])
            };
            allowed = runtime_type_predicate_intersect(&allowed, &sig_allowed);
        }
        for sig in &clause.neg {
            if sig.is_exact_empty() {
                allowed = runtime_type_predicate_remove(&allowed, &ListShape::Empty);
            } else if sig.is_exact_non_empty() {
                allowed = runtime_type_predicate_remove(&allowed, &ListShape::NonEmpty);
            }
        }
        out = out.union(&allowed);
    }
    out
}

fn runtime_type_predicate_tuple_arities(descr: &Descr) -> ObservedSet<usize> {
    let mut out = ObservedSet::none();
    for clause in &descr.tuples {
        let mut allowed = if clause.pos.is_empty() {
            ObservedSet::any()
        } else {
            let arities = clause.pos.iter().map(|sig| sig.elems.len()).collect::<BTreeSet<_>>();
            if arities.len() != 1 {
                continue;
            }
            ObservedSet::lit(*arities.iter().next().expect("one tuple arity"))
        };
        for sig in &clause.neg {
            allowed = runtime_type_predicate_remove(&allowed, &sig.elems.len());
        }
        out = out.union(&allowed);
    }
    out
}

fn runtime_type_predicate_named_structs(descr: &Descr) -> ObservedSet<String> {
    const STRUCT_PREFIX: &str = "impl-target::";
    ObservedSet::finite(
        descr
            .opaques
            .set
            .iter()
            .filter_map(|tag| tag.strip_prefix(STRUCT_PREFIX).map(str::to_string)),
    )
}

fn runtime_type_predicate_intersect<T>(left: &ObservedSet<T>, right: &ObservedSet<T>) -> ObservedSet<T>
where
    T: Ord + Clone,
{
    match (left.cofinite, right.cofinite) {
        (false, false) => ObservedSet::finite(left.values.intersection(&right.values).cloned()),
        (true, false) => ObservedSet::finite(right.values.difference(&left.values).cloned()),
        (false, true) => ObservedSet::finite(left.values.difference(&right.values).cloned()),
        (true, true) => ObservedSet::cofinite(left.values.union(&right.values).cloned()),
    }
}

fn runtime_type_predicate_remove<T>(set: &ObservedSet<T>, value: &T) -> ObservedSet<T>
where
    T: Ord + Clone,
{
    if set.cofinite {
        let mut excluded = set.values.clone();
        excluded.insert(value.clone());
        ObservedSet::cofinite(excluded)
    } else {
        ObservedSet::finite(set.values.iter().filter(|candidate| *candidate != value).cloned())
    }
}

fn specialize_callable_clause(
    types: &mut Types,
    clause: &CallableClause<Ty>,
    surface: &CallableClause<Ty>,
) -> CallableClause<Ty> {
    let mut sigma = Sigma::new();
    for (pattern, witness) in clause.args.iter().zip(surface.args.iter()) {
        types.collect_instantiation_subst(pattern, witness, &mut sigma);
    }
    types.collect_instantiation_subst(&clause.ret, &surface.ret, &mut sigma);
    CallableClause {
        args: clause.args.iter().map(|arg| types.instantiate(arg, &sigma)).collect(),
        ret: types.instantiate(&clause.ret, &sigma),
        closure: clause.closure.clone(),
    }
}

fn has_vars(cx: TyCtx<'_>, d: &Descr) -> bool {
    if !d.vars.set.is_empty() {
        return true;
    }
    d.tuples.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.elems.iter().any(|t| has_vars(cx, cx.descr(t))))
    }) || d.lists.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.elem.is_some_and(|t| has_vars(cx, cx.descr(&t))))
    }) || d.resources.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| has_vars(cx, cx.descr(&sig.payload)))
    }) || d.funcs.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.args.iter().any(|t| has_vars(cx, cx.descr(t))) || has_vars(cx, cx.descr(&sig.ret)))
    }) || d.maps.iter().any(|c| {
        c.pos
            .iter()
            .chain(c.neg.iter())
            .any(|sig| sig.fields.values().any(|t| has_vars(cx, cx.descr(t))))
    })
}

fn as_pure_list<'a>(cx: TyCtx<'a>, d: &'a Descr) -> Option<&'a ListSig> {
    d.as_pure_list(cx)
}

fn arrow_join_return(cx: TyCtx<'_>, d: &Descr) -> Descr {
    if d.funcs.is_empty() {
        return Descr::any();
    }
    let mut acc = Descr::none();
    for c in &d.funcs {
        if !c.neg.is_empty() || c.pos.is_empty() {
            return Descr::any();
        }
        for sig in &c.pos {
            acc = acc.union(cx, cx.descr(&sig.ret));
        }
    }
    acc
}

#[cfg(test)]
fn tuple_lit_elems(cx: TyCtx<'_>, d: &Descr) -> Option<Vec<Ty>> {
    let elems = d.as_tuple_singleton()?;
    elems.iter().all(|t| is_literal(cx, t)).then(|| elems.to_vec())
}

#[cfg(test)]
fn is_literal(cx: TyCtx<'_>, a: &Ty) -> bool {
    let d = cx.descr(a);
    d.is_singleton_literal()
        || d.is_equiv(cx, &Descr::nil())
        || tuple_lit_elems(cx, d).is_some()
        || d.as_closure_lit()
            .is_some_and(|lit| lit.captures.iter().all(|capture| is_literal(cx, capture)))
}

// More recursive transforms live in this module so they can thread the owning
// interner explicitly without exposing the private descriptor representation.
fn widen_for_recursive_spec_key(t: &mut Types, a: Ty) -> Descr {
    let base = t.descr(&a).widen_literals();
    map_recursive_inputs(t, base, widen_for_recursive_spec_key)
}

fn erase_closure_identity(t: &mut Types, a: Ty) -> Descr {
    let base = t.descr(&a).clone();
    map_recursive_inputs(t, base, erase_closure_identity).without_closure_lits()
}

fn refine_widen(t: &mut Types, a: Ty, b: Ty) -> Descr {
    let lhs = t.descr(&a).clone();
    let rhs = t.descr(&b).clone();
    if let (Some(l), Some(r)) = (lhs.pure_tuple().cloned(), rhs.pure_tuple().cloned())
        && l.elems.len() == r.elems.len()
    {
        let elems: Vec<Ty> = l
            .elems
            .iter()
            .zip(r.elems.iter())
            .map(|(l, r)| {
                let d = refine_widen(t, *l, *r);
                t.intern(d)
            })
            .collect();
        return Descr::tuple_of(elems);
    }
    if let (Some(l), Some(r)) = (lhs.as_pure_list(t.ctx()).cloned(), rhs.as_pure_list(t.ctx()).cloned()) {
        let elem = match (l.elem, r.elem) {
            (Some(l), Some(r)) => {
                let d = refine_widen(t, l, r);
                Some(t.intern(d))
            }
            (Some(l), None) => Some(l),
            (None, Some(r)) => Some(r),
            (None, None) => None,
        };
        return match elem {
            Some(elem) => Descr::list_sig(ListSig {
                empty: l.empty || r.empty,
                elem: Some(elem),
            }),
            None => Descr::empty_list(),
        };
    }
    if let (Some(l), Some(r)) = (lhs.pure_resource().cloned(), rhs.pure_resource().cloned()) {
        let d = refine_widen(t, l.payload, r.payload);
        let payload = t.intern(d);
        return Descr::resource_of(t.ctx(), payload);
    }
    if let (Some(l), Some(r)) = (lhs.pure_arrow().cloned(), rhs.pure_arrow().cloned())
        && l.args.len() == r.args.len()
    {
        let args: Vec<Ty> = l.args.iter().zip(r.args.iter()).map(|(l, r)| t.union(*l, *r)).collect();
        let d = refine_widen(t, l.ret, r.ret);
        let ret = t.intern(d);
        return Descr::arrow(args, ret);
    }
    if let (Some(l), Some(r)) = (lhs.pure_map().cloned(), rhs.pure_map().cloned()) {
        let mut fields = l.fields.clone();
        for (key, rv) in &r.fields {
            if let Some(lv) = fields.get_mut(key) {
                let d = refine_widen(t, *lv, *rv);
                *lv = t.intern(d);
            } else {
                fields.insert(key.clone(), *rv);
            }
        }
        return Descr::map_of(fields);
    }

    let u = t.union(a, b);
    widen_for_recursive_spec_key(t, u)
}

fn alpha_normalize_vars(t: &mut Types, a: Ty) -> Descr {
    let mut sigma = std::collections::BTreeMap::new();
    let mut next = 0;
    alpha_normalize_go(t, a, &mut sigma, &mut next)
}

fn alpha_normalize_go(
    t: &mut Types,
    a: Ty,
    sigma: &mut std::collections::BTreeMap<TypeVarId, TypeVarId>,
    next: &mut u32,
) -> Descr {
    fn mapped_id(
        old: TypeVarId,
        sigma: &mut std::collections::BTreeMap<TypeVarId, TypeVarId>,
        next: &mut u32,
    ) -> TypeVarId {
        if let Some(mapped) = sigma.get(&old) {
            return *mapped;
        }
        let fresh = TypeVarId(*next);
        *next += 1;
        sigma.insert(old, fresh);
        fresh
    }

    let mut out = t.descr(&a).clone();
    if !out.vars.is_any() {
        out.vars.set = out
            .vars
            .set
            .iter()
            .copied()
            .map(|id| mapped_id(id, sigma, next))
            .collect();
    }
    map_recursive_inputs_with(t, out, &mut |t, nested| {
        let d = alpha_normalize_go(t, nested, sigma, next);
        t.intern(d)
    })
}

fn instantiate(t: &mut Types, a: Ty, sigma: &Sigma<Ty>) -> Descr {
    let d = t.descr(&a).clone();
    if !has_vars(t.ctx(), &d) {
        return d;
    }
    let mut substituted = Descr::none();
    let mut base = d.clone();
    if !base.vars.cofinite {
        let mut new_set = BTreeSet::new();
        for id in &d.vars.set {
            match sigma.get(id) {
                Some(replacement) => {
                    substituted = substituted.union(t.ctx(), t.descr(replacement));
                }
                None => {
                    new_set.insert(*id);
                }
            }
        }
        base.vars = LiteralSet {
            set: new_set,
            cofinite: false,
        };
    }
    let walked = map_recursive_inputs_with(t, base, &mut |t, nested| {
        let d = instantiate(t, nested, sigma);
        t.intern(d)
    });
    walked.union(t.ctx(), &substituted)
}

fn collect_subst_into(t: &mut Types, pattern: Ty, witness: Ty, sigma: &mut Sigma<Ty>) {
    let pat = t.descr(&pattern).clone();
    let wit = t.descr(&witness).clone();
    if let Some(ids) = pure_var_ids(&pat) {
        for id in ids {
            sigma.entry(id).or_insert(witness);
        }
        return;
    }
    if let (Some(ps), Some(ws)) = (pat.pure_tuple(), wit.pure_tuple())
        && ps.elems.len() == ws.elems.len()
    {
        for (p, w) in ps.elems.iter().zip(ws.elems.iter()) {
            collect_subst_into(t, *p, *w, sigma);
        }
    }
    if let (Some(ps), Some(ws)) = (pat.as_pure_list(t.ctx()), wit.as_pure_list(t.ctx()))
        && let (Some(p), Some(w)) = (ps.elem, ws.elem)
    {
        collect_subst_into(t, p, w, sigma);
    }
    if let (Some(ps), Some(ws)) = (pat.pure_resource(), wit.pure_resource()) {
        collect_subst_into(t, ps.payload, ws.payload, sigma);
    }
    if let (Some(ps), Some(ws)) = (pat.pure_arrow(), wit.pure_arrow())
        && ps.args.len() == ws.args.len()
    {
        for (p, w) in ps.args.iter().zip(ws.args.iter()) {
            collect_subst_into(t, *p, *w, sigma);
        }
        collect_subst_into(t, ps.ret, ws.ret, sigma);
    }
    if let (Some(ps), Some(ws)) = (pat.pure_map(), wit.pure_map()) {
        for (key, p) in &ps.fields {
            if let Some(w) = ws.fields.get(key) {
                collect_subst_into(t, *p, *w, sigma);
            }
        }
    }
}

fn map_recursive_inputs(t: &mut Types, d: Descr, f: fn(&mut Types, Ty) -> Descr) -> Descr {
    map_recursive_inputs_with(t, d, &mut |t, nested| {
        let d = f(t, nested);
        t.intern(d)
    })
}

fn map_recursive_inputs_with(t: &mut Types, mut d: Descr, f: &mut impl FnMut(&mut Types, Ty) -> Ty) -> Descr {
    for conj in &mut d.tuples {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.elems = sig.elems.iter().map(|ty| f(t, *ty)).collect();
        }
    }
    for conj in &mut d.lists {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.elem = sig.elem.map(|ty| f(t, ty));
        }
    }
    for conj in &mut d.resources {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.payload = f(t, sig.payload);
        }
    }
    for conj in &mut d.funcs {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.args = sig.args.iter().map(|ty| f(t, *ty)).collect();
            sig.ret = f(t, sig.ret);
        }
    }
    for conj in &mut d.maps {
        for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
            sig.fields = sig.fields.iter().map(|(k, v)| (k.clone(), f(t, *v))).collect();
        }
    }
    d
}

fn mint_owned_resource_aliases_descr(cx: TyCtx<'_>, d: &Descr, candidates: &[(String, Descr)]) -> Descr {
    for (tag, inner) in candidates {
        if resource_payload_type(cx, d).is_some_and(|payload| payload.is_equiv(cx, inner)) {
            return Descr::opaque_of(tag);
        }
    }
    d.clone()
}

#[cfg(test)]
mod types_test;
