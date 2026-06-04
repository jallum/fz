//! Interned set-theoretic type implementation.
//!
//! This module intentionally duplicates the concrete type kernel instead of
//! depending on `concrete_types::Descr`. Its `Descr` is private here, and every
//! structural child is an `InternedTy` allocated by the owning
//! `InternedConcreteTypes` instance.

mod bits;
mod conj;
mod descr;
mod dnf;
mod emptiness;
mod format;
mod lit_set;
mod sigs;

use std::collections::{BTreeSet, HashMap};

use crate::type_expr::opaque_owner_module;
use crate::types::{
    CallableClause, ClosureLitInfo, ClosureTarget, ClosureTypes, MapKey, Nominals, OpaqueVisibilityError, RenderTypes,
    Sigma, TypeVarId, Types, VisibilityTypes,
};

use conj::Conj;
use descr::Descr;
use lit_set::{LiteralSet, closure_ret_var_id, closure_var_id};
use sigs::{ArrowSig, ClosureLit, ListSig};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct InternedTy(u32);

#[derive(Default)]
pub struct InternedConcreteTypes {
    interner: TypeInterner,
}

#[derive(Default)]
struct TypeInterner {
    arena: Vec<Descr>,
    index: HashMap<Descr, InternedTy>,
}

#[derive(Clone, Copy)]
pub(super) struct TyCtx<'a> {
    arena: &'a [Descr],
}

impl<'a> TyCtx<'a> {
    fn descr(&self, t: &InternedTy) -> &'a Descr {
        self.arena
            .get(t.0 as usize)
            .unwrap_or_else(|| panic!("unknown interned type id {}", t.0))
    }
}

impl TypeInterner {
    fn intern(&mut self, d: Descr) -> InternedTy {
        if let Some(ty) = self.index.get(&d) {
            return *ty;
        }
        let raw = self.arena.len();
        assert!(u32::try_from(raw).is_ok(), "type interner exhausted ids");
        let ty = InternedTy(raw as u32);
        self.arena.push(d.clone());
        self.index.insert(d, ty);
        ty
    }

    fn ctx(&self) -> TyCtx<'_> {
        TyCtx { arena: &self.arena }
    }

    fn descr(&self, t: &InternedTy) -> &Descr {
        self.ctx().descr(t)
    }
}

impl InternedConcreteTypes {
    pub fn new() -> Self {
        Self::default()
    }

    fn intern(&mut self, d: Descr) -> InternedTy {
        self.interner.intern(d)
    }

    fn ctx(&self) -> TyCtx<'_> {
        self.interner.ctx()
    }

    fn descr(&self, t: &InternedTy) -> &Descr {
        self.interner.descr(t)
    }

    fn descr_inner_map(&self, m: &HashMap<String, InternedTy>) -> HashMap<String, Descr> {
        m.iter().map(|(k, v)| (k.clone(), self.descr(v).clone())).collect()
    }
}

impl Types for InternedConcreteTypes {
    type Ty = InternedTy;

    fn any(&mut self) -> InternedTy {
        self.intern(Descr::any())
    }

    fn none(&mut self) -> InternedTy {
        self.intern(Descr::none())
    }

    fn nil(&mut self) -> InternedTy {
        self.intern(Descr::nil())
    }

    fn bool(&mut self) -> InternedTy {
        self.intern(Descr::bool_t())
    }

    fn int(&mut self) -> InternedTy {
        self.intern(Descr::int())
    }

    fn int_lit(&mut self, n: i64) -> InternedTy {
        self.intern(Descr::int_lit(n))
    }

    fn float(&mut self) -> InternedTy {
        self.intern(Descr::float())
    }

    fn float_lit(&mut self, f: f64) -> InternedTy {
        self.intern(Descr::float_lit(f))
    }

    fn atom(&mut self) -> InternedTy {
        self.intern(Descr::atom_top())
    }

    fn atom_lit(&mut self, name: &str) -> InternedTy {
        self.intern(Descr::atom_lit(name))
    }

    fn type_var(&mut self, id: TypeVarId) -> InternedTy {
        self.intern(Descr::var(id))
    }

    fn resource(&mut self, payload: InternedTy) -> InternedTy {
        self.intern(Descr::resource_of(self.ctx(), payload))
    }

    fn arrow(&mut self, args: &[InternedTy], ret: InternedTy) -> InternedTy {
        self.intern(Descr::arrow(args.iter().copied(), ret))
    }

    fn tuple(&mut self, elems: &[InternedTy]) -> InternedTy {
        self.intern(Descr::tuple_of(elems.iter().copied()))
    }

    fn empty_list(&mut self) -> InternedTy {
        self.intern(Descr::empty_list())
    }

    fn list(&mut self, elem: InternedTy) -> InternedTy {
        self.intern(Descr::list_of(self.ctx(), elem))
    }

    fn non_empty_list(&mut self, elem: InternedTy) -> InternedTy {
        self.intern(Descr::non_empty_list_of(self.ctx(), elem))
    }

    fn map(&mut self, fields: &[(MapKey, InternedTy)]) -> InternedTy {
        self.intern(Descr::map_of(fields.iter().cloned()))
    }

    fn str_t(&mut self) -> InternedTy {
        self.intern(Descr::str_t())
    }

    fn map_top(&mut self) -> InternedTy {
        self.intern(Descr::map_top())
    }

    fn mint_brand(&mut self, inner: InternedTy, name: &str) -> InternedTy {
        let mut d = self.descr(&inner).clone();
        d.brands = LiteralSet::lit(name.to_string());
        self.intern(d)
    }

    fn opaque_of(&mut self, name: &str) -> InternedTy {
        self.intern(Descr::opaque_of(name))
    }

    fn brand_of(&mut self, name: &str) -> InternedTy {
        self.intern(Descr::brand_of(name))
    }

    fn list_element_type(&mut self, a: &InternedTy) -> InternedTy {
        let d = {
            let cx = self.ctx();
            list_element_type(cx, cx.descr(a))
        };
        self.intern(d)
    }

    fn has_list_shape(&self, a: &InternedTy) -> bool {
        !self.descr(a).lists.is_empty()
    }

    fn resource_payload_type(&mut self, a: &InternedTy) -> Option<InternedTy> {
        let d = {
            let cx = self.ctx();
            resource_payload_type(cx, cx.descr(a))?
        };
        Some(self.intern(d))
    }

    fn mint_owned_resource_aliases(
        &mut self,
        a: InternedTy,
        owner: &str,
        opaque_inners: &HashMap<String, InternedTy>,
    ) -> InternedTy {
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

    fn tuple_projections(&mut self, a: &InternedTy, arity: usize) -> Vec<InternedTy> {
        let ds = {
            let cx = self.ctx();
            tuple_projections(cx, cx.descr(a), arity)
        };
        ds.into_iter().map(|d| self.intern(d)).collect()
    }

    fn tuple_field_type(&mut self, a: &InternedTy, index: usize) -> InternedTy {
        let d = {
            let cx = self.ctx();
            tuple_field_type(cx, cx.descr(a), index)
        };
        self.intern(d)
    }

    fn max_tuple_arity(&self, a: &InternedTy) -> usize {
        self.descr(a).max_tuple_arity()
    }

    fn refine_map_field(&mut self, a: &InternedTy, key: &MapKey, v: &InternedTy) -> InternedTy {
        let d = self.descr(a).refine_map_field(key, *v);
        self.intern(d)
    }

    fn map_field_lookup(&mut self, a: &InternedTy, key: &MapKey) -> Option<InternedTy> {
        let d = {
            let cx = self.ctx();
            map_field_lookup(cx, cx.descr(a), key)?
        };
        Some(self.intern(d))
    }

    fn map_known_keys(&self, a: &InternedTy) -> Vec<MapKey> {
        map_known_keys(self.descr(a))
    }

    fn widen_for_recursive_spec_key(&mut self, a: &InternedTy) -> InternedTy {
        let d = widen_for_recursive_spec_key(self, *a);
        self.intern(d)
    }

    fn alpha_normalize_vars(&mut self, a: &InternedTy) -> InternedTy {
        let d = alpha_normalize_vars(self, *a);
        self.intern(d)
    }

    fn refine_widen(&mut self, a: &InternedTy, b: &InternedTy) -> InternedTy {
        let d = refine_widen(self, *a, *b);
        self.intern(d)
    }

    fn convergence_class(&mut self, a: &InternedTy) -> InternedTy {
        if as_pure_list(self.ctx(), self.descr(a)).is_some() {
            let any = self.any();
            self.list(any)
        } else {
            *a
        }
    }

    fn union(&mut self, a: InternedTy, b: InternedTy) -> InternedTy {
        let d = {
            let cx = self.ctx();
            cx.descr(&a).union(cx, cx.descr(&b))
        };
        self.intern(d)
    }

    fn intersect(&mut self, a: InternedTy, b: InternedTy) -> InternedTy {
        let d = self.descr(&a).intersect(self.descr(&b));
        self.intern(d)
    }

    #[cfg(test)]
    fn complement(&mut self, a: InternedTy) -> InternedTy {
        let d = self.descr(&a).neg();
        self.intern(d)
    }

    fn difference(&mut self, a: InternedTy, b: InternedTy) -> InternedTy {
        let d = self.descr(&a).diff(self.descr(&b));
        self.intern(d)
    }

    fn is_empty(&self, a: &InternedTy) -> bool {
        let cx = self.ctx();
        self.descr(a).is_empty(cx)
    }

    #[cfg(test)]
    fn is_top(&self, a: &InternedTy) -> bool {
        let cx = self.ctx();
        self.descr(a).is_equiv(cx, &Descr::any())
    }

    fn is_subtype(&self, a: &InternedTy, b: &InternedTy) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, self.descr(b))
    }

    fn is_disjoint(&self, a: &InternedTy, b: &InternedTy) -> bool {
        let cx = self.ctx();
        self.descr(a).intersect(self.descr(b)).is_empty(cx)
    }

    fn is_value_disjoint(&self, a: &InternedTy, b: &InternedTy, nominals: Nominals<'_, InternedTy>) -> bool {
        let bi = self.descr_inner_map(nominals.brand_inners);
        let oi = self.descr_inner_map(nominals.opaque_inners);
        let cx = self.ctx();
        self.descr(a).value_disjoint(cx, self.descr(b), Nominals::new(&bi, &oi))
    }

    fn key_var_count(&self, key: &[InternedTy]) -> usize {
        key.iter().map(|t| self.descr(t).vars.finite_len().unwrap_or(0)).sum()
    }

    fn key_subsumes_with(&self, query: &InternedTy, key: &InternedTy, sigma: &mut Sigma<InternedTy>) -> bool {
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

    fn kinds_overlap(&self, a: &InternedTy, b: &InternedTy) -> bool {
        self.descr(a).kinds_overlap(self.descr(b))
    }

    fn opaque_singleton(&self, a: &InternedTy) -> Option<String> {
        self.descr(a).as_opaque_singleton().map(String::from)
    }

    #[cfg(test)]
    fn brand_singleton(&self, a: &InternedTy) -> Option<String> {
        self.descr(a).as_brand_singleton().map(String::from)
    }

    fn is_singleton_lit(&self, a: &InternedTy) -> bool {
        self.descr(a).is_singleton_literal()
    }

    fn as_int_singleton(&self, a: &InternedTy) -> Option<i64> {
        self.descr(a).as_int_singleton()
    }

    fn as_float_singleton(&self, a: &InternedTy) -> Option<f64> {
        self.descr(a).as_float_singleton().map(|b| b.get())
    }

    fn as_atom_singleton(&self, a: &InternedTy) -> Option<String> {
        self.descr(a).as_atom_singleton().map(String::from)
    }

    fn arrow_join_return(&mut self, a: &InternedTy) -> InternedTy {
        let d = {
            let cx = self.ctx();
            arrow_join_return(cx, cx.descr(a))
        };
        self.intern(d)
    }

    #[cfg(test)]
    fn tuple_lit_elems(&self, a: &InternedTy) -> Option<Vec<InternedTy>> {
        tuple_lit_elems(self.ctx(), self.descr(a))
    }

    fn is_integer(&self, a: &InternedTy) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::int())
    }

    fn is_floating(&self, a: &InternedTy) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::float())
    }

    fn is_nil(&self, a: &InternedTy) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::nil())
    }

    #[cfg(test)]
    fn is_bool(&self, a: &InternedTy) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::bool_t())
    }

    #[cfg(test)]
    fn is_atom_type(&self, a: &InternedTy) -> bool {
        let cx = self.ctx();
        self.descr(a).is_subtype(cx, &Descr::atom_top())
    }

    fn has_vars(&self, a: &InternedTy) -> bool {
        has_vars(self.ctx(), self.descr(a))
    }

    fn instantiate(&mut self, a: &InternedTy, sigma: &Sigma<InternedTy>) -> InternedTy {
        let d = instantiate(self, *a, sigma);
        self.intern(d)
    }

    fn collect_instantiation_subst(
        &mut self,
        pattern: &InternedTy,
        witness: &InternedTy,
        sigma: &mut Sigma<InternedTy>,
    ) {
        collect_subst_into(self, *pattern, *witness, sigma);
    }
}

impl ClosureTypes for InternedConcreteTypes {
    fn fn_ref_lit(&mut self, target: ClosureTarget, n_args: usize) -> InternedTy {
        let fn_id = target.into();
        let args: Vec<InternedTy> = (0..n_args)
            .map(|pos| self.intern(Descr::var(closure_var_id(fn_id, pos))))
            .collect();
        let ret = self.intern(Descr::var(closure_ret_var_id(fn_id)));
        self.intern(Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args,
                ret,
                lit: Some(ClosureLit {
                    kind: crate::types::CallableValueKind::FnRef,
                    fn_id,
                    captures: Vec::new(),
                }),
            })],
            ..Descr::none()
        })
    }

    fn closure_lit(&mut self, target: ClosureTarget, captures: Vec<InternedTy>, n_args: usize) -> InternedTy {
        let fn_id = target.into();
        let args: Vec<InternedTy> = (0..n_args)
            .map(|pos| self.intern(Descr::var(closure_var_id(fn_id, pos))))
            .collect();
        let ret = self.intern(Descr::var(closure_ret_var_id(fn_id)));
        self.intern(Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args,
                ret,
                lit: Some(ClosureLit {
                    kind: crate::types::CallableValueKind::Closure,
                    fn_id,
                    captures,
                }),
            })],
            ..Descr::none()
        })
    }

    fn closure_lit_parts(&self, a: &InternedTy) -> Option<ClosureLitInfo<InternedTy>> {
        let lit = self.descr(a).as_closure_lit()?;
        Some(ClosureLitInfo {
            target: lit.fn_id.into(),
            captures: lit.captures.clone(),
            kind: lit.kind,
        })
    }

    fn callable_clauses(&mut self, a: &InternedTy) -> Option<Vec<CallableClause<InternedTy>>> {
        callable_clauses(self.ctx(), self.descr(a))
    }

    fn erase_closure_identity(&mut self, a: &InternedTy) -> InternedTy {
        let d = erase_closure_identity(self, *a);
        self.intern(d)
    }
}

impl VisibilityTypes for InternedConcreteTypes {
    fn check_opaque_visibility(&self, a: &InternedTy, using_module: &str) -> Result<(), OpaqueVisibilityError> {
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

impl RenderTypes for InternedConcreteTypes {
    fn display(&self, a: &InternedTy) -> String {
        format::display(self.ctx(), self.descr(a))
    }

    fn display_for_diag(&self, a: &InternedTy) -> String {
        format::display_for_diag(self.ctx(), self.descr(a))
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

fn callable_clauses(cx: TyCtx<'_>, d: &Descr) -> Option<Vec<CallableClause<InternedTy>>> {
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
fn tuple_lit_elems(cx: TyCtx<'_>, d: &Descr) -> Option<Vec<InternedTy>> {
    let elems = d.as_tuple_singleton()?;
    elems.iter().all(|t| is_literal(cx, t)).then(|| elems.to_vec())
}

#[cfg(test)]
fn is_literal(cx: TyCtx<'_>, a: &InternedTy) -> bool {
    let d = cx.descr(a);
    d.is_singleton_literal()
        || d.is_equiv(cx, &Descr::nil())
        || tuple_lit_elems(cx, d).is_some()
        || d.as_closure_lit()
            .is_some_and(|lit| lit.captures.iter().all(|capture| is_literal(cx, capture)))
}

// More recursive transforms live in this module so they can thread the owning
// interner explicitly without exposing the private descriptor representation.
fn widen_for_recursive_spec_key(t: &mut InternedConcreteTypes, a: InternedTy) -> Descr {
    let base = t.descr(&a).widen_literals();
    map_recursive_inputs(t, base, widen_for_recursive_spec_key)
}

fn erase_closure_identity(t: &mut InternedConcreteTypes, a: InternedTy) -> Descr {
    let base = t.descr(&a).clone();
    map_recursive_inputs(t, base, erase_closure_identity).without_closure_lits()
}

fn refine_widen(t: &mut InternedConcreteTypes, a: InternedTy, b: InternedTy) -> Descr {
    let lhs = t.descr(&a).clone();
    let rhs = t.descr(&b).clone();
    if let (Some(l), Some(r)) = (lhs.pure_tuple().cloned(), rhs.pure_tuple().cloned())
        && l.elems.len() == r.elems.len()
    {
        let elems: Vec<InternedTy> = l
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
        let args: Vec<InternedTy> = l.args.iter().zip(r.args.iter()).map(|(l, r)| t.union(*l, *r)).collect();
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

fn alpha_normalize_vars(t: &mut InternedConcreteTypes, a: InternedTy) -> Descr {
    let mut sigma = std::collections::BTreeMap::new();
    let mut next = 0;
    alpha_normalize_go(t, a, &mut sigma, &mut next)
}

fn alpha_normalize_go(
    t: &mut InternedConcreteTypes,
    a: InternedTy,
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

fn instantiate(t: &mut InternedConcreteTypes, a: InternedTy, sigma: &Sigma<InternedTy>) -> Descr {
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

fn collect_subst_into(
    t: &mut InternedConcreteTypes,
    pattern: InternedTy,
    witness: InternedTy,
    sigma: &mut Sigma<InternedTy>,
) {
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

fn map_recursive_inputs(
    t: &mut InternedConcreteTypes,
    d: Descr,
    f: fn(&mut InternedConcreteTypes, InternedTy) -> Descr,
) -> Descr {
    map_recursive_inputs_with(t, d, &mut |t, nested| {
        let d = f(t, nested);
        t.intern(d)
    })
}

fn map_recursive_inputs_with(
    t: &mut InternedConcreteTypes,
    mut d: Descr,
    f: &mut impl FnMut(&mut InternedConcreteTypes, InternedTy) -> InternedTy,
) -> Descr {
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
mod interned_types_test;
