//! Set-theoretic type descriptors.
//!
//! A `Descr` represents a set of values. The lattice has top (`any` — every
//! value) and bottom (`none` — no value), and is closed under union,
//! intersection, and complement.
//!
//! Representation follows Castagna 2024 / Frisch-Castagna-Benzaken 2008 and
//! mirrors the shape of Elixir's `Module.Types.Descr`:
//!
//!   Descr = bitmap of basic types
//!         ∪ set of atom literals (finite OR cofinite)
//!         ∪ DNF over tuple shapes
//!         ∪ DNF over list-of-T shapes
//!         ∪ DNF over function arrows
//!
//! "Basic" types are scalars with no internal structure to vary over (`int`,
//! `float`, `nil`, `bool`, and `str`). Atoms get their
//! own field because we want literal atom types (`:ok`, `:error`) — a
//! BasicBits flag for "atom" alone wouldn't let us express that.
//!
//! Operations (union/intersect/diff/neg) work componentwise: bitwise on the
//! basic bitmap, finite/cofinite arithmetic on the atom set, DNF
//! manipulation (concat / cross-product / De Morgan) on the structurals.
//! Semantic subtyping — `T <: U` iff `T ∧ ¬U` is empty — lands in fz-ul4.3.

mod bits;
mod conj;
mod descr;
mod dnf;
mod emptiness;
mod format;
mod lit_set;
mod sigs;
mod views;

use std::collections::HashMap;

use crate::types::{
    CallableClause, ClosureLitInfo, ClosureTarget, ClosureTypes, MapKey, OpaqueVisibilityError,
    RenderTypes, Sigma, Ty, TypeVarId, Types, VisibilityTypes,
};

use conj::Conj;
pub(crate) use descr::Descr;
pub(crate) use lit_set::LiteralSet;
use sigs::{ArrowSig, ListSig, MapSig, ResourceSig, TupleSig};
pub(crate) use views::Component;

pub(crate) fn ty_from_descr(d: Descr) -> Ty {
    Ty(std::sync::Arc::new(d))
}

pub(crate) fn ty_descr(t: &Ty) -> &Descr {
    &t.0
}

/// Convert a `Ty`-keyed inner-type map (as carried by `Module`) into the
/// `Descr`-keyed form `Descr::erase_nominal` consumes. The maps are tiny
/// (one entry per declared brand/opaque), so the per-call clone is cheap.
fn descr_inner_map(m: &HashMap<String, Ty>) -> HashMap<String, Descr> {
    m.iter()
        .map(|(k, v)| (k.clone(), ty_descr(v).clone()))
        .collect()
}

pub(crate) fn ty_display(t: &Ty) -> String {
    format!("{}", ty_descr(t))
}

impl ConcreteTypes {
    pub(crate) fn display(&self, a: &Ty) -> String {
        <Self as RenderTypes>::display(self, a)
    }
}

/// Day-one implementation: thin wrapper around `Descr`. Zero fields —
/// it's an oracle, not a store. Future implementations will hold
/// interning tables, memo caches, or BDD nodes.
#[derive(Debug)]
pub struct ConcreteTypes;

impl Types for ConcreteTypes {
    type Ty = Ty;

    fn any(&mut self) -> Ty {
        ty_from_descr(Descr::any())
    }
    fn none(&mut self) -> Ty {
        ty_from_descr(Descr::none())
    }
    fn nil(&mut self) -> Ty {
        ty_from_descr(Descr::nil())
    }
    fn bool(&mut self) -> Ty {
        ty_from_descr(Descr::bool_t())
    }
    fn bool_lit(&mut self, b: bool) -> Ty {
        ty_from_descr(Descr::atom_lit(if b { "true" } else { "false" }))
    }
    fn int(&mut self) -> Ty {
        ty_from_descr(Descr::int())
    }
    fn int_lit(&mut self, n: i64) -> Ty {
        ty_from_descr(Descr::int_lit(n))
    }
    fn float(&mut self) -> Ty {
        ty_from_descr(Descr::float())
    }
    fn float_lit(&mut self, f: f64) -> Ty {
        ty_from_descr(Descr::float_lit(f))
    }
    fn atom(&mut self) -> Ty {
        ty_from_descr(Descr::atom_top())
    }
    fn atom_lit(&mut self, name: &str) -> Ty {
        ty_from_descr(Descr::atom_lit(name))
    }
    fn type_var(&mut self, id: TypeVarId) -> Ty {
        ty_from_descr(Descr::var(id))
    }
    fn cpointer(&mut self) -> Ty {
        ty_from_descr(Descr::opaque_of("cpointer"))
    }
    fn resource(&mut self, payload: Ty) -> Ty {
        ty_from_descr(Descr::resource_of(ty_descr(&payload).clone()))
    }
    fn arrow(&mut self, args: &[Ty], ret: Ty) -> Ty {
        let args: Vec<Descr> = args.iter().map(|t| ty_descr(t).clone()).collect();
        ty_from_descr(Descr::arrow(args, ty_descr(&ret).clone()))
    }
    fn tuple(&mut self, elems: &[Ty]) -> Ty {
        let elems: Vec<Descr> = elems.iter().map(|t| ty_descr(t).clone()).collect();
        ty_from_descr(Descr::tuple_of(elems))
    }
    fn empty_list(&mut self) -> Ty {
        ty_from_descr(Descr::empty_list())
    }
    fn list(&mut self, elem: Ty) -> Ty {
        ty_from_descr(Descr::list_of(ty_descr(&elem).clone()))
    }
    fn non_empty_list(&mut self, elem: Ty) -> Ty {
        ty_from_descr(Descr::non_empty_list_of(ty_descr(&elem).clone()))
    }
    fn map(&mut self, fields: &[(MapKey, Ty)]) -> Ty {
        let fields: Vec<(MapKey, Descr)> = fields
            .iter()
            .map(|(k, t)| (k.clone(), ty_descr(t).clone()))
            .collect();
        ty_from_descr(Descr::map_of(fields))
    }
    fn str_t(&mut self) -> Ty {
        ty_from_descr(Descr::str_t())
    }
    fn map_top(&mut self) -> Ty {
        ty_from_descr(Descr::map_top())
    }
    fn mint_brand(&mut self, inner: Ty, name: &str) -> Ty {
        let mut d = ty_descr(&inner).clone();
        d.brands = LiteralSet::lit(name.to_string());
        ty_from_descr(d)
    }
    fn opaque_of(&mut self, name: &str) -> Ty {
        ty_from_descr(Descr::opaque_of(name))
    }
    fn brand_of(&mut self, name: &str) -> Ty {
        ty_from_descr(Descr::brand_of(name))
    }
    fn list_element_type(&mut self, a: &Ty) -> Ty {
        concrete_list_element_type(a)
    }
    fn has_list_shape(&self, a: &Ty) -> bool {
        ty_descr(a)
            .components()
            .any(|component| matches!(component, Component::Lists(_)))
    }
    fn resource_payload_type(&mut self, a: &Ty) -> Option<Ty> {
        for component in ty_descr(a).components() {
            if let Component::Resources(view) = component {
                return Some(ty_from_descr(view.payload_type()));
            }
        }
        None
    }
    fn mint_owned_resource_aliases(
        &mut self,
        a: Ty,
        owner: &str,
        opaque_inners: &HashMap<String, Ty>,
    ) -> Ty {
        let _top_level_resource = self.resource_payload_type(&a);
        let candidates = opaque_inners
            .iter()
            .filter_map(|(tag, inner)| {
                let tag_owner = crate::type_expr::opaque_owner_module(tag)?;
                (tag_owner == owner).then(|| (tag.clone(), ty_descr(inner).clone()))
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return a;
        }
        ty_from_descr(mint_owned_resource_aliases_descr(ty_descr(&a), &candidates))
    }
    fn tuple_projections(&mut self, a: &Ty, arity: usize) -> Vec<Ty> {
        concrete_tuple_projections(a, arity)
    }
    fn max_tuple_arity(&self, a: &Ty) -> usize {
        ty_descr(a).max_tuple_arity()
    }
    fn refine_map_field(&mut self, a: &Ty, key: &MapKey, v: &Ty) -> Ty {
        concrete_refine_map_field(a, key, v)
    }
    fn map_field_lookup(&mut self, a: &Ty, key: &MapKey) -> Option<Ty> {
        concrete_map_field_lookup(a, key)
    }
    fn map_known_keys(&self, a: &Ty) -> Vec<MapKey> {
        concrete_map_known_keys(a)
    }
    fn widen_for_recursive_spec_key(&mut self, a: &Ty) -> Ty {
        ty_from_descr(ty_descr(a).widen_for_recursive_spec_key())
    }
    fn union(&mut self, a: Ty, b: Ty) -> Ty {
        ty_from_descr(ty_descr(&a).union(ty_descr(&b)))
    }
    fn intersect(&mut self, a: Ty, b: Ty) -> Ty {
        ty_from_descr(ty_descr(&a).intersect(ty_descr(&b)))
    }
    #[cfg(test)]
    fn complement(&mut self, a: Ty) -> Ty {
        ty_from_descr(ty_descr(&a).neg())
    }
    fn difference(&mut self, a: Ty, b: Ty) -> Ty {
        ty_from_descr(ty_descr(&a).diff(ty_descr(&b)))
    }
    fn is_empty(&self, a: &Ty) -> bool {
        ty_descr(a).is_empty()
    }
    fn is_top(&self, a: &Ty) -> bool {
        ty_descr(a).is_equiv(&Descr::any())
    }
    fn is_subtype(&self, a: &Ty, b: &Ty) -> bool {
        ty_descr(a).is_subtype(ty_descr(b))
    }
    fn is_disjoint(&self, a: &Ty, b: &Ty) -> bool {
        ty_descr(a).intersect(ty_descr(b)).is_empty()
    }
    fn is_value_disjoint(&self, a: &Ty, b: &Ty, nominals: crate::types::Nominals<'_, Ty>) -> bool {
        let bi = descr_inner_map(nominals.brand_inners);
        let oi = descr_inner_map(nominals.opaque_inners);
        ty_descr(a).value_disjoint(ty_descr(b), crate::types::Nominals::new(&bi, &oi))
    }
    fn is_equivalent(&self, a: &Ty, b: &Ty) -> bool {
        ty_descr(a).is_equiv(ty_descr(b))
    }
    fn key_var_count(&self, key: &[Ty]) -> usize {
        key.iter()
            .map(|t| {
                ty_descr(t)
                    .components()
                    .filter_map(|c| match c {
                        Component::Vars(v) => v.finite_len(),
                        _ => None,
                    })
                    .sum::<usize>()
            })
            .sum()
    }
    fn key_subsumes_with(&self, query: &Ty, key: &Ty, sigma: &mut Sigma<Ty>) -> bool {
        fn pure_var_ids(d: &Descr) -> Option<Vec<TypeVarId>> {
            let mut comps = d.components();
            let only = comps.next()?;
            if comps.next().is_some() {
                return None;
            }
            match only {
                Component::Vars(view) => {
                    let finite: Vec<TypeVarId> = view.finite()?.collect();
                    if finite.is_empty() {
                        None
                    } else {
                        Some(finite)
                    }
                }
                _ => None,
            }
        }
        let qd = ty_descr(query);
        let kd = ty_descr(key);
        if kd.looks_full() {
            return true;
        }
        if let Some(alphas) = pure_var_ids(kd) {
            for alpha in alphas {
                match sigma.get(&alpha) {
                    None => {
                        sigma.insert(alpha, query.clone());
                    }
                    Some(existing) => {
                        if !ty_descr(existing).is_equiv(qd) {
                            return false;
                        }
                    }
                }
            }
            return true;
        }
        qd.is_subtype(kd)
    }
    fn kinds_overlap(&self, a: &Ty, b: &Ty) -> bool {
        ty_descr(a).kinds_overlap(ty_descr(b))
    }
    fn opaque_singleton(&self, a: &Ty) -> Option<String> {
        ty_descr(a).as_opaque_singleton().map(String::from)
    }
    #[cfg(test)]
    fn brand_singleton(&self, a: &Ty) -> Option<String> {
        ty_descr(a).as_brand_singleton().map(String::from)
    }
    fn is_singleton_lit(&self, a: &Ty) -> bool {
        ty_descr(a).is_singleton_literal()
    }
    fn as_int_singleton(&self, a: &Ty) -> Option<i64> {
        ty_descr(a).as_int_singleton()
    }
    fn as_float_singleton(&self, a: &Ty) -> Option<f64> {
        ty_descr(a).as_float_singleton().map(|b| b.get())
    }
    fn as_atom_singleton(&self, a: &Ty) -> Option<String> {
        ty_descr(a).as_atom_singleton().map(String::from)
    }
    fn arrow_join_return(&mut self, a: &Ty) -> Ty {
        ty_from_descr(ty_descr(a).arrow_join_return())
    }
    fn tuple_lit_elems(&self, a: &Ty) -> Option<Vec<Ty>> {
        concrete_tuple_lit_elems(a)
    }
    fn as_map_key(&self, a: &Ty) -> Option<MapKey> {
        ty_descr(a).as_map_key()
    }
    fn is_empty_list_lit(&self, a: &Ty) -> bool {
        ty_descr(a).is_equiv(&Descr::empty_list())
    }
    fn is_integer(&self, a: &Ty) -> bool {
        ty_descr(a).is_subtype(&Descr::int())
    }
    fn is_floating(&self, a: &Ty) -> bool {
        ty_descr(a).is_subtype(&Descr::float())
    }
    fn is_nil(&self, a: &Ty) -> bool {
        ty_descr(a).is_subtype(&Descr::nil())
    }
    #[cfg(test)]
    fn is_bool(&self, a: &Ty) -> bool {
        ty_descr(a).is_subtype(&Descr::bool_t())
    }
    #[cfg(test)]
    fn is_atom_type(&self, a: &Ty) -> bool {
        ty_descr(a).is_subtype(&Descr::atom_top())
    }
    fn has_vars(&self, a: &Ty) -> bool {
        ty_descr(a).has_vars()
    }
    fn mentioned_type_vars(&self, a: &Ty) -> std::collections::BTreeSet<TypeVarId> {
        ty_descr(a).mentioned_type_vars()
    }
    fn is_strictly_smaller(&self, a: &Ty, p: &Ty) -> bool {
        if let (Some(ai), Some(pi)) = (self.as_int_singleton(a), self.as_int_singleton(p)) {
            if pi > 0 && ai >= 0 && ai < pi {
                return true;
            }
            if pi < 0 && ai <= 0 && ai > pi {
                return true;
            }
        }
        ty_descr(a).recursive_spec_depth() < ty_descr(p).recursive_spec_depth()
    }
    fn instantiate(&mut self, a: &Ty, sigma: &Sigma<Ty>) -> Ty {
        let inner: HashMap<TypeVarId, Descr> = sigma
            .iter()
            .map(|(id, t)| (*id, ty_descr(t).clone()))
            .collect();
        ty_from_descr(ty_descr(a).instantiate(&inner))
    }
    fn collect_instantiation_subst(&mut self, pattern: &Ty, witness: &Ty, sigma: &mut Sigma<Ty>) {
        let mut inner: HashMap<TypeVarId, Descr> = sigma
            .iter()
            .map(|(id, t)| (*id, ty_descr(t).clone()))
            .collect();
        Descr::collect_subst_into(ty_descr(pattern), ty_descr(witness), &mut inner);
        *sigma = inner
            .into_iter()
            .map(|(id, d)| (id, ty_from_descr(d)))
            .collect();
    }
}

fn mint_owned_resource_aliases_descr(d: &Descr, candidates: &[(String, Descr)]) -> Descr {
    for (tag, inner) in candidates {
        if resource_payload_matches(d, inner) {
            return Descr::opaque_of(tag);
        }
    }

    let mut out = d.clone();
    out.tuples = out
        .tuples
        .into_iter()
        .map(|c| mint_tuple_conj(c, candidates))
        .collect();
    out.lists = out
        .lists
        .into_iter()
        .map(|c| mint_list_conj(c, candidates))
        .collect();
    out.resources = out
        .resources
        .into_iter()
        .map(|c| mint_resource_conj(c, candidates))
        .collect();
    out.funcs = out
        .funcs
        .into_iter()
        .map(|c| mint_arrow_conj(c, candidates))
        .collect();
    out.maps = out
        .maps
        .into_iter()
        .map(|c| mint_map_conj(c, candidates))
        .collect();
    out
}

fn descr_equivalent(a: &Descr, b: &Descr) -> bool {
    a.diff(b).is_empty() && b.diff(a).is_empty()
}

fn resource_payload_matches(d: &Descr, inner: &Descr) -> bool {
    d.components().any(|component| {
        if let Component::Resources(view) = component {
            descr_equivalent(&view.payload_type(), inner)
        } else {
            false
        }
    })
}

fn mint_tuple_conj(c: Conj<TupleSig>, candidates: &[(String, Descr)]) -> Conj<TupleSig> {
    Conj {
        pos: c
            .pos
            .into_iter()
            .map(|sig| TupleSig {
                elems: sig
                    .elems
                    .iter()
                    .map(|elem| mint_owned_resource_aliases_descr(elem, candidates))
                    .collect(),
            })
            .collect(),
        neg: c
            .neg
            .into_iter()
            .map(|sig| TupleSig {
                elems: sig
                    .elems
                    .iter()
                    .map(|elem| mint_owned_resource_aliases_descr(elem, candidates))
                    .collect(),
            })
            .collect(),
    }
}

fn mint_list_conj(c: Conj<ListSig>, candidates: &[(String, Descr)]) -> Conj<ListSig> {
    Conj {
        pos: c
            .pos
            .into_iter()
            .map(|sig| ListSig {
                empty: sig.empty,
                elem: sig
                    .elem
                    .map(|elem| Box::new(mint_owned_resource_aliases_descr(&elem, candidates))),
            })
            .collect(),
        neg: c
            .neg
            .into_iter()
            .map(|sig| ListSig {
                empty: sig.empty,
                elem: sig
                    .elem
                    .map(|elem| Box::new(mint_owned_resource_aliases_descr(&elem, candidates))),
            })
            .collect(),
    }
}

fn mint_resource_conj(c: Conj<ResourceSig>, candidates: &[(String, Descr)]) -> Conj<ResourceSig> {
    Conj {
        pos: c
            .pos
            .into_iter()
            .map(|sig| ResourceSig {
                payload: Box::new(mint_owned_resource_aliases_descr(&sig.payload, candidates)),
            })
            .collect(),
        neg: c
            .neg
            .into_iter()
            .map(|sig| ResourceSig {
                payload: Box::new(mint_owned_resource_aliases_descr(&sig.payload, candidates)),
            })
            .collect(),
    }
}

fn mint_arrow_conj(c: Conj<ArrowSig>, candidates: &[(String, Descr)]) -> Conj<ArrowSig> {
    Conj {
        pos: c
            .pos
            .into_iter()
            .map(|sig| ArrowSig {
                args: sig
                    .args
                    .iter()
                    .map(|arg| mint_owned_resource_aliases_descr(arg, candidates))
                    .collect(),
                ret: Box::new(mint_owned_resource_aliases_descr(&sig.ret, candidates)),
                lit: sig.lit.map(|lit| sigs::ClosureLit {
                    fn_id: lit.fn_id,
                    captures: lit
                        .captures
                        .into_iter()
                        .map(|capture| {
                            ty_from_descr(mint_owned_resource_aliases_descr(
                                ty_descr(&capture),
                                candidates,
                            ))
                        })
                        .collect(),
                }),
            })
            .collect(),
        neg: c
            .neg
            .into_iter()
            .map(|sig| ArrowSig {
                args: sig
                    .args
                    .iter()
                    .map(|arg| mint_owned_resource_aliases_descr(arg, candidates))
                    .collect(),
                ret: Box::new(mint_owned_resource_aliases_descr(&sig.ret, candidates)),
                lit: sig.lit.map(|lit| sigs::ClosureLit {
                    fn_id: lit.fn_id,
                    captures: lit
                        .captures
                        .into_iter()
                        .map(|capture| {
                            ty_from_descr(mint_owned_resource_aliases_descr(
                                ty_descr(&capture),
                                candidates,
                            ))
                        })
                        .collect(),
                }),
            })
            .collect(),
    }
}

fn mint_map_conj(c: Conj<MapSig>, candidates: &[(String, Descr)]) -> Conj<MapSig> {
    Conj {
        pos: c
            .pos
            .into_iter()
            .map(|sig| MapSig {
                fields: sig
                    .fields
                    .into_iter()
                    .map(|(key, value)| {
                        (key, mint_owned_resource_aliases_descr(&value, candidates))
                    })
                    .collect(),
            })
            .collect(),
        neg: c
            .neg
            .into_iter()
            .map(|sig| MapSig {
                fields: sig
                    .fields
                    .into_iter()
                    .map(|(key, value)| {
                        (key, mint_owned_resource_aliases_descr(&value, candidates))
                    })
                    .collect(),
            })
            .collect(),
    }
}

impl ClosureTypes for ConcreteTypes {
    fn closure_lit(&mut self, target: ClosureTarget, captures: Vec<Ty>, n_args: usize) -> Ty {
        let capture_descrs: Vec<Descr> =
            captures.into_iter().map(|c| ty_descr(&c).clone()).collect();
        ty_from_descr(Descr::closure_lit(target.into(), capture_descrs, n_args))
    }

    fn closure_lit_parts(&self, a: &Ty) -> Option<ClosureLitInfo<Ty>> {
        let lit = ty_descr(a).as_closure_lit()?;
        Some(ClosureLitInfo {
            target: lit.fn_id.into(),
            captures: lit.captures.clone(),
        })
    }

    fn callable_clauses(&mut self, a: &Ty) -> Option<Vec<CallableClause<Ty>>> {
        let funcs_view = ty_descr(a).components().find_map(|c| match c {
            Component::Funcs(v) => Some(v),
            _ => None,
        })?;
        if funcs_view.has_negations() || !funcs_view.all_clauses_have_pos() {
            return None;
        }
        Some(
            funcs_view
                .arrows()
                .map(|arrow| CallableClause {
                    args: arrow.args().iter().cloned().map(ty_from_descr).collect(),
                    ret: ty_from_descr(arrow.ret().clone()),
                    closure: arrow.closure_lit().map(|lit| ClosureLitInfo {
                        target: lit.fn_id.into(),
                        captures: lit.captures.clone(),
                    }),
                })
                .collect(),
        )
    }
}

impl VisibilityTypes for ConcreteTypes {
    fn check_opaque_visibility(
        &self,
        a: &Ty,
        using_module: &str,
    ) -> Result<(), OpaqueVisibilityError> {
        let Some(tag) = ty_descr(a).as_opaque_singleton() else {
            return Ok(());
        };
        let Some(owner) = crate::type_expr::opaque_owner_module(tag) else {
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

impl RenderTypes for ConcreteTypes {
    fn display(&self, a: &Ty) -> String {
        format!("{}", ty_descr(a))
    }

    fn display_for_diag(&self, a: &Ty) -> String {
        ty_descr(a).display_for_diag()
    }
}

fn concrete_list_element_type(a: &Ty) -> Ty {
    for component in ty_descr(a).components() {
        if let Component::Lists(view) = component {
            return ty_from_descr(view.element_type());
        }
    }
    ty_from_descr(Descr::any())
}

fn concrete_tuple_projections(a: &Ty, arity: usize) -> Vec<Ty> {
    for component in ty_descr(a).components() {
        if let Component::Tuples(view) = component
            && let Some(comps) = view.project_all(arity)
        {
            return comps.into_iter().map(ty_from_descr).collect();
        }
    }
    vec![ty_from_descr(Descr::any()); arity]
}

fn concrete_map_field_lookup(a: &Ty, key: &MapKey) -> Option<Ty> {
    for component in ty_descr(a).components() {
        if let Component::Maps(view) = component {
            return view.lookup(key).map(ty_from_descr);
        }
    }
    None
}

fn concrete_map_known_keys(a: &Ty) -> Vec<MapKey> {
    let mut keys = std::collections::BTreeSet::new();
    for component in ty_descr(a).components() {
        let Component::Maps(view) = component else {
            continue;
        };
        for conj in view.inner {
            for sig in &conj.pos {
                keys.extend(sig.fields.keys().cloned());
            }
        }
    }
    keys.into_iter().collect()
}

fn concrete_refine_map_field(a: &Ty, key: &MapKey, v: &Ty) -> Ty {
    ty_from_descr(ty_descr(a).refine_map_field(key, ty_descr(v)))
}

fn concrete_tuple_lit_elems(a: &Ty) -> Option<Vec<Ty>> {
    let elems = ty_descr(a).as_tuple_singleton()?;
    let elems: Vec<Ty> = elems.iter().cloned().map(ty_from_descr).collect();
    elems.iter().all(concrete_is_literal).then_some(elems)
}

fn concrete_is_literal(a: &Ty) -> bool {
    ty_descr(a).is_singleton_literal()
        || ty_descr(a).is_equiv(&Descr::nil())
        || concrete_tuple_lit_elems(a).is_some()
        || ty_descr(a)
            .as_closure_lit()
            .is_some_and(|lit| lit.captures.iter().all(concrete_is_literal))
}

#[cfg(test)]
mod tests;
