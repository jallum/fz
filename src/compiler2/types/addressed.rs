//! Addressed type variables and the addressed-arrow builder.
//!
//! A type variable's canonical identity is its *structural address* in a
//! signature, not an encounter-order counter:
//!
//! ```text
//! @spec foo(a, {b, c}, d)   -->  (a0, {a1_0, a1_1}, a2) -> r0
//! @spec flibble(t, t) :: t  -->  (a0, a0) -> a0
//! ```
//!
//! parameter `i` addresses to `a{i}`; the result slot to `r0`; component `j`
//! of the slot at address `P` to `P_j`. A *name*'s canonical id is the address
//! of its **first occurrence** (pre-order: params left-to-right, result last);
//! repeats reuse it. Because the address is the structural path, `d` in `foo`
//! is `a2` regardless of how many fields the second parameter's tuple holds —
//! adding a field never renumbers `d`. This is what encounter-order numbering
//! cannot express — it would call `d` `a3` and drift when the tuple grows — and
//! is why the addressed arrow replaced it outright (fz-hwn.27.8 retired the last
//! encounter canonicalizer, `alpha_normalize_vars`).
//!
//! Addresses are interned ([`Types::address_id`]) so that
//! [`Types::param_alpha`]`(0)` always yields the same `a0`: structurally
//! identical signatures build byte-identical arrows, and the hash-consing
//! interner folds each alpha-equivalence class to one integer by construction.
//!
//! This is the construction-root machinery for the Addressed Arrow (fz-hwn.27);
//! it lands beside the old per-position normalization and is wired into the
//! resolver (fz-hwn.27.3) and the activation-key mint (fz-hwn.27.6) later.

use std::collections::{BTreeSet, HashMap};

use super::descr::Descr;
use super::{Ty, TypeVarId, Types};
use crate::finite_set::FiniteSet;

/// One step of a structural address. A full address is a `&[AddrStep]` path
/// rooted at a parameter or the result slot.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AddrStep {
    /// Parameter `i` of the arrow (top level).
    Param(u16),
    /// The arrow's result slot.
    Result,
    /// Capture `i` of a closure literal attached to the current arrow.
    Capture(u16),
    /// Field `j` of the tuple at the current address.
    Field(u16),
    /// Alternative `k` of a tuple union at the current address.
    Variant(u16),
    /// The element of the list at the current address.
    Elem,
    /// The payload of the resource at the current address.
    Payload,
    /// Field `j` (by position) of the map at the current address.
    MapField(u16),
    /// Disambiguator for the `k`-th variable when a single node carries a
    /// union of several variables (rare in signatures).
    VarSlot(u16),
}

/// Which binder owns addresses encountered while walking a type.
///
/// Ordinary values are embedded in the surrounding slot, so even an address
/// left by a prior surface is rewritten under that slot. `ArrowSig::args` and
/// `ArrowSig::ret` form an explicit callable binder of their own; addresses
/// already established inside that surface remain stable when the callable is
/// embedded elsewhere.
#[derive(Clone, Copy, PartialEq, Eq)]
enum AddressOwner {
    EmbeddedValue,
    CallableSurface,
    CapturedValue,
}

#[derive(Default)]
struct AddressCorrelations {
    /// Variables owned by the addressed value surface as a whole.
    values: HashMap<TypeVarId, TypeVarId>,
    /// One correlation frame per enclosing callable binder.
    binders: Vec<BinderCorrelations>,
}

#[derive(Default)]
struct BinderCorrelations {
    /// Originals that participate in this arrow's args or result.
    surface: HashMap<TypeVarId, TypeVarId>,
    /// Originals introduced by this arrow's literal captures.
    captures: HashMap<TypeVarId, TypeVarId>,
}

/// The `TypeVarId` space is partitioned by its top bit so a var's KIND is
/// intrinsic to its id, with no out-of-band lookup. Bit 31 SET means a
/// structural address (minted here by [`Types::address_id`]); bit 31 CLEAR
/// means a free var — a closure-surface var (`closure_var_id`, `fn_id*64+pos`),
/// a resolver encounter var, or a typedef param. The two kinds densely overlap
/// the low range otherwise (`closure_var_id(0, 0) == 0 ==` the first address),
/// so the tag is what lets display render `a0`/`r0` for canonical addresses and
/// `αN` for free vars without guessing (fz-hwn.27.13). `closure_var_id` asserts
/// it never reaches the tag, which only tightens the `fn_id * 64` < `u32`
/// invariant the closure-var stride already relies on.
pub(super) const ADDRESS_TAG: u32 = 0x8000_0000;

/// The structural address path behind an interned address id, or `None` when
/// `id` is a free var (the tag is clear). The dense address index is the id
/// with its tag masked off, so the reverse table is a flat `Vec` lookup.
pub(super) fn address_path(paths: &[Vec<AddrStep>], id: TypeVarId) -> Option<&[AddrStep]> {
    if id.0 & ADDRESS_TAG == 0 {
        return None;
    }
    let index = (id.0 & !ADDRESS_TAG) as usize;
    paths.get(index).map(Vec::as_slice)
}

/// Render a structural address path for display: the root step names the slot
/// (`a{i}` for parameter `i`, `r0` for the result), and each nested step appends
/// `_<component>` so `[Param(1), Field(0)]` reads `a1_0` and `[Result, Elem]`
/// reads `r0_e` (fz-hwn.27.13). A legible mirror of the `AddrStep` path, never a
/// hard type — purely diagnostic.
pub(super) fn format_address(path: &[AddrStep]) -> String {
    let mut out = String::new();
    for (i, step) in path.iter().enumerate() {
        match (i, step) {
            (0, AddrStep::Param(p)) => out.push_str(&format!("a{p}")),
            (0, AddrStep::Result) => out.push_str("r0"),
            (_, AddrStep::Param(p)) => out.push_str(&format!("_p{p}")),
            (_, AddrStep::Result) => out.push_str("_r"),
            (_, AddrStep::Capture(c)) => out.push_str(&format!("_c{c}")),
            // Every path is rooted at a Param or Result slot, so index 0 is
            // always one of the two arms above; nested component steps only ever
            // appear after the root.
            (_, AddrStep::Field(j)) | (_, AddrStep::MapField(j)) => out.push_str(&format!("_{j}")),
            (_, AddrStep::Variant(k)) => out.push_str(&format!("_u{k}")),
            (_, AddrStep::VarSlot(k)) => out.push_str(&format!("_v{k}")),
            (_, AddrStep::Elem) => out.push_str("_e"),
            (_, AddrStep::Payload) => out.push_str("_p"),
        }
    }
    out
}

impl Types {
    /// Intern a structural address to its canonical [`TypeVarId`]. Same address
    /// always yields the same id, so `param_alpha(0)` is stable across every
    /// signature built by this `Types` instance. The id carries [`ADDRESS_TAG`]
    /// so it is structurally distinguishable from a free var, and its dense
    /// index (the tag masked off) keys the [`Types::address_paths`] reverse
    /// table that display reads back.
    pub fn address_id(&mut self, path: &[AddrStep]) -> TypeVarId {
        if let Some(&id) = self.address_vars.get(path) {
            return id;
        }
        let index = self.address_vars.len() as u32;
        debug_assert!(index < ADDRESS_TAG, "address-id space exhausted below the tag bit");
        let id = TypeVarId(ADDRESS_TAG | index);
        self.address_vars.insert(path.to_vec(), id);
        self.address_paths.push(path.to_vec());
        id
    }

    /// The interned type variable living at a structural address.
    pub fn address_var(&mut self, path: &[AddrStep]) -> Ty {
        let id = self.address_id(path);
        self.type_var(id)
    }

    /// `a{i}` — the variable at parameter slot `i`.
    pub fn param_alpha(&mut self, i: usize) -> Ty {
        self.address_var(&[AddrStep::Param(i as u16)])
    }

    /// The `TypeVarId` of `a{i}` — the key consumers use to read a parameter
    /// slot's bound out of a [`ResolvedArrow`](crate::compiler2::resolve)'s
    /// bounds map without naming the `AddrStep` path.
    pub fn param_alpha_id(&mut self, i: usize) -> TypeVarId {
        self.address_id(&[AddrStep::Param(i as u16)])
    }

    /// `r0` — the variable at the result slot.
    pub fn result_alpha(&mut self) -> Ty {
        self.address_var(&[AddrStep::Result])
    }

    /// The `TypeVarId` of `r0` — the result slot's address key.
    pub fn result_alpha_id(&mut self) -> TypeVarId {
        self.address_id(&[AddrStep::Result])
    }

    /// Build the canonical addressed arrow for a signature. Each original
    /// variable is mapped to the address of its first occurrence (pre-order:
    /// `params[0..]` depth-first, then `result`); repeats reuse that address.
    /// Concrete structure (tuples, lists, brands, refinements) is preserved
    /// exactly — only variable identity is canonicalized.
    pub fn address_arrow(&mut self, params: &[Ty], result: Ty) -> Ty {
        self.address_arrow_with_env(params, result).0
    }

    /// Address an input vector among ITSELF — params left-to-right, sharing one
    /// substitution so a variable that recurs across inputs reuses its
    /// first-occurrence param address. No result slot participates, so the
    /// inputs map into the param-address space (`a0`, `a1`, …), disjoint from the
    /// result address `r0`. This is the activation-key / surface canonicalizer:
    /// the inputs are canonical by construction (whole-scope, one pass), and the
    /// interner folds two same-shape vectors to one identity — no separate
    /// normalization pass exists. The key's `r0` result is appended by the
    /// caller and cannot collide with an input address.
    pub fn address_inputs(&mut self, inputs: &[Ty]) -> Vec<Ty> {
        let mut correlations = AddressCorrelations::default();
        inputs
            .iter()
            .enumerate()
            .map(|(i, &p)| self.address_remap(p, &[AddrStep::Param(i as u16)], &mut correlations))
            .collect()
    }

    /// The OWN-SURFACE of a closure activation arrow: its parameter slots past
    /// the `captures_len` leading capture slots, re-addressed standalone. A
    /// closure activation surface is `(cap0..capK, param0..)` — the captures are
    /// leading addressed slots and the params are the suffix (fz-hwn.27.8). The
    /// suffix carries `a{K}..` addresses in the full arrow's frame; re-addressing
    /// rebases it to the canonical `a0`-based surface frame, so two closures that
    /// share a body but differ in captures yield one own-surface, comparable to a
    /// standalone `CallableSurface`. Idempotent when `captures_len` is 0.
    pub fn own_surface(&mut self, activation_inputs: &[Ty], captures_len: usize) -> Vec<Ty> {
        self.address_inputs(&activation_inputs[captures_len..])
    }

    /// The own-surface of a closure activation that carries `addressed_captures`
    /// as its leading slots, or `None` when it does not — a different closure
    /// instance (fz-hwn.27.8). `addressed_captures` is the captures addressed
    /// standalone; by the left-to-right addressing property it is exactly the
    /// activation arrow's leading capture prefix, so prefix equality decides
    /// capture identity and the suffix re-addresses to the own-surface.
    pub fn own_surface_past_captures(
        &mut self,
        activation_inputs: &[Ty],
        addressed_captures: &[Ty],
    ) -> Option<Vec<Ty>> {
        let captures_len = addressed_captures.len();
        (activation_inputs.len() >= captures_len && activation_inputs[..captures_len] == *addressed_captures)
            .then(|| self.own_surface(activation_inputs, captures_len))
    }

    /// As [`address_arrow`](Self::address_arrow), but also returns the
    /// original-id -> address-id map. Callers re-key sidecars (variable bounds,
    /// human names) onto addresses through this map so they stay aligned with
    /// the canonical arrow.
    pub fn address_arrow_with_env(&mut self, params: &[Ty], result: Ty) -> (Ty, HashMap<TypeVarId, TypeVarId>) {
        let mut correlations = AddressCorrelations::default();
        let params: Vec<Ty> = params
            .iter()
            .enumerate()
            .map(|(i, &p)| self.address_remap(p, &[AddrStep::Param(i as u16)], &mut correlations))
            .collect();
        let result = self.address_remap(result, &[AddrStep::Result], &mut correlations);
        let arrow = self.arrow(&params, result);
        (arrow, correlations.values)
    }

    /// Rewrite every variable in `ty` to its first-occurrence address, threading
    /// the explicit value/binder correlation scopes so repeats share only in
    /// their owning scope, and recursing with the address path extended.
    fn address_remap(&mut self, ty: Ty, path: &[AddrStep], correlations: &mut AddressCorrelations) -> Ty {
        self.address_remap_with(ty, path, correlations, AddressOwner::EmbeddedValue)
    }

    fn address_remap_with(
        &mut self,
        ty: Ty,
        path: &[AddrStep],
        correlations: &mut AddressCorrelations,
        owner: AddressOwner,
    ) -> Ty {
        if !self.has_vars(&ty) {
            return ty;
        }
        let mut d = self.descr(&ty).clone();
        if !d.vars.cofinite && !d.vars.values.is_empty() {
            d.vars = self.address_vars_at(&d.vars, path, correlations, owner);
        }
        self.address_remap_children(&mut d, path, correlations, owner);
        self.intern(d)
    }

    /// Map the finite variable set living at one node to address ids. A single
    /// variable takes the node's address; a union of several takes `VarSlot(k)`
    /// sub-addresses so distinct variables never collide.
    fn address_vars_at(
        &mut self,
        vars: &FiniteSet<TypeVarId>,
        path: &[AddrStep],
        correlations: &mut AddressCorrelations,
        owner: AddressOwner,
    ) -> FiniteSet<TypeVarId> {
        let originals: Vec<TypeVarId> = vars.values.iter().copied().collect();
        let single = originals.len() == 1;
        let mut set = BTreeSet::new();
        for (k, original) in originals.into_iter().enumerate() {
            let mapped = if owner == AddressOwner::CallableSurface {
                let binder = correlations
                    .binders
                    .last_mut()
                    .expect("callable surface has a correlation scope");
                if let Some(&id) = binder.surface.get(&original) {
                    id
                } else {
                    let id = if address_path(&self.address_paths, original).is_some() {
                        original
                    } else if let Some(&id) = correlations.values.get(&original) {
                        id
                    } else {
                        let id = if single {
                            self.address_id(path)
                        } else {
                            let mut child = path.to_vec();
                            child.push(AddrStep::VarSlot(k as u16));
                            self.address_id(&child)
                        };
                        correlations.values.insert(original, id);
                        id
                    };
                    binder.surface.insert(original, id);
                    id
                }
            } else if owner == AddressOwner::CapturedValue
                && let Some(id) = correlations
                    .binders
                    .iter()
                    .rev()
                    .find_map(|binder| binder.surface.get(&original).copied())
            {
                id
            } else if owner == AddressOwner::CapturedValue
                && let Some(id) = correlations
                    .binders
                    .last()
                    .and_then(|binder| binder.captures.get(&original).copied())
            {
                id
            } else if owner == AddressOwner::CapturedValue
                && let Some(binder) = correlations.binders.last_mut()
            {
                let id = if single {
                    self.address_id(path)
                } else {
                    let mut child = path.to_vec();
                    child.push(AddrStep::VarSlot(k as u16));
                    self.address_id(&child)
                };
                binder.captures.insert(original, id);
                id
            } else if let Some(&id) = correlations.values.get(&original) {
                id
            } else {
                let id = if single {
                    self.address_id(path)
                } else {
                    let mut child = path.to_vec();
                    child.push(AddrStep::VarSlot(k as u16));
                    self.address_id(&child)
                };
                correlations.values.insert(original, id);
                id
            };
            set.insert(mapped);
        }
        FiniteSet::finite(set)
    }

    /// Recurse into every nested shape of `d`, including a closure literal's
    /// environment captures, extending the address path by the structural step
    /// at each child (mirrors `map_recursive_inputs_with`, but path-aware).
    fn address_remap_children(
        &mut self,
        d: &mut Descr,
        path: &[AddrStep],
        correlations: &mut AddressCorrelations,
        owner: AddressOwner,
    ) {
        let tuple_alternatives = d
            .tuples
            .iter()
            .map(|conj| conj.pos.len() + conj.neg.len())
            .sum::<usize>();
        let discriminate_tuple_alternatives = tuple_alternatives > 1;
        let mut tuple_alternative = 0_u16;
        for conj in &mut d.tuples {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                let alternative = tuple_alternative;
                tuple_alternative = tuple_alternative.saturating_add(1);
                for (j, ty) in sig.elems.iter_mut().enumerate() {
                    let mut child = path.to_vec();
                    if discriminate_tuple_alternatives {
                        child.push(AddrStep::Variant(alternative));
                    }
                    child.push(AddrStep::Field(j as u16));
                    *ty = self.address_remap_with(*ty, &child, correlations, owner);
                }
            }
        }
        for conj in &mut d.lists {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                if let Some(elem) = sig.elem {
                    let mut child = path.to_vec();
                    child.push(AddrStep::Elem);
                    sig.elem = Some(self.address_remap_with(elem, &child, correlations, owner));
                }
            }
        }
        for conj in &mut d.resources {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                let mut child = path.to_vec();
                child.push(AddrStep::Payload);
                sig.payload = self.address_remap_with(sig.payload, &child, correlations, owner);
            }
        }
        for conj in &mut d.funcs {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                correlations.binders.push(BinderCorrelations::default());
                for (i, ty) in sig.args.iter_mut().enumerate() {
                    let mut child = path.to_vec();
                    child.push(AddrStep::Param(i as u16));
                    *ty = self.address_remap_with(*ty, &child, correlations, AddressOwner::CallableSurface);
                }
                let mut child = path.to_vec();
                child.push(AddrStep::Result);
                sig.ret = self.address_remap_with(sig.ret, &child, correlations, AddressOwner::CallableSurface);
                if let Some(lit) = &mut sig.lit {
                    for (i, capture) in lit.captures.iter_mut().enumerate() {
                        let mut child = path.to_vec();
                        child.push(AddrStep::Capture(i as u16));
                        *capture = self.address_remap_with(*capture, &child, correlations, AddressOwner::CapturedValue);
                    }
                }
                correlations.binders.pop().expect("callable correlation scope");
            }
        }
        for conj in &mut d.maps {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                for (j, (_, ty)) in sig.fields.iter_mut().enumerate() {
                    let mut child = path.to_vec();
                    child.push(AddrStep::MapField(j as u16));
                    *ty = self.address_remap_with(*ty, &child, correlations, owner);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::conj::Conj;
    use super::super::sigs::{ArrowSig, ClosureLit};
    use super::super::{CallableValueKind, ClosureTarget};
    use super::AddrStep::{Elem, Field, Param, VarSlot, Variant};
    use super::*;
    use crate::compiler2::identity::{ActivationKey, FunctionId, RootId};
    use crate::compiler2::semantic::SemanticOrd;

    fn var(t: &mut Types, id: u32) -> Ty {
        t.type_var(TypeVarId(id))
    }

    #[test]
    fn distinct_params_do_not_conflate_with_repeated_params() {
        // The defect this dissolves: (a, b) must not collapse to (a, a).
        let mut t = Types::new();
        let x = var(&mut t, 100);
        let y = var(&mut t, 101);
        let int = t.int();
        let ab = t.address_arrow(&[x, y], int);
        let aa = t.address_arrow(&[x, x], int);
        assert_ne!(ab, aa, "(a, b) and (a, a) must be distinct interned arrows");
    }

    #[test]
    fn repeated_name_unifies_to_the_first_occurrence_address() {
        // flibble(t, t) :: t  -->  (a0, a0) -> a0
        let mut t = Types::new();
        let tv = var(&mut t, 5);
        let arrow = t.address_arrow(&[tv, tv], tv);
        let a0 = t.param_alpha(0);
        let expected = t.arrow(&[a0, a0], a0);
        assert_eq!(arrow, expected);
    }

    #[test]
    fn nested_components_address_by_path() {
        // foo(a, {b, c}, d)  -->  (a0, {a1_0, a1_1}, a2) -> r0
        let mut t = Types::new();
        let a = var(&mut t, 10);
        let b = var(&mut t, 11);
        let c = var(&mut t, 12);
        let d = var(&mut t, 13);
        let r = var(&mut t, 14); // unnamed result
        let tup = t.tuple(&[b, c]);
        let foo = t.address_arrow(&[a, tup, d], r);

        let a0 = t.param_alpha(0);
        let a1_0 = t.address_var(&[Param(1), Field(0)]);
        let a1_1 = t.address_var(&[Param(1), Field(1)]);
        let a2 = t.param_alpha(2);
        let r0 = t.result_alpha();
        let etup = t.tuple(&[a1_0, a1_1]);
        let expected = t.arrow(&[a0, etup, a2], r0);
        assert_eq!(foo, expected);
    }

    #[test]
    fn input_to_result_identity_is_preserved() {
        // (a, b) -> b stays (a, b) -> b, never (a, b) -> a.
        let mut t = Types::new();
        let x = var(&mut t, 20);
        let y = var(&mut t, 21);
        let arrow = t.address_arrow(&[x, y], y);
        let a0 = t.param_alpha(0);
        let a1 = t.param_alpha(1);
        let right = t.arrow(&[a0, a1], a1);
        let wrong = t.arrow(&[a0, a1], a0);
        assert_eq!(arrow, right, "result must reuse the second parameter's address");
        assert_ne!(arrow, wrong, "result must not collapse onto the first parameter");
    }

    #[test]
    fn parameter_address_is_independent_of_sibling_arity() {
        // d is a2 whether the second parameter's tuple has two fields or three.
        let mut t = Types::new();
        let a = var(&mut t, 30);
        let b = var(&mut t, 31);
        let c = var(&mut t, 32);
        let e = var(&mut t, 33);
        let d = var(&mut t, 34);
        let r2 = var(&mut t, 35);
        let r3 = var(&mut t, 36);
        let tup2 = t.tuple(&[b, c]);
        let foo2 = t.address_arrow(&[a, tup2, d], r2);
        let tup3 = t.tuple(&[b, c, e]);
        let foo3 = t.address_arrow(&[a, tup3, d], r3);

        let a2 = t.param_alpha(2);
        let arg2_of_foo2 = t.callable_clauses(&foo2).unwrap()[0].args[2];
        let arg2_of_foo3 = t.callable_clauses(&foo3).unwrap()[0].args[2];
        assert_eq!(arg2_of_foo2, a2);
        assert_eq!(arg2_of_foo3, a2, "growing the sibling tuple must not renumber d");
    }

    #[test]
    fn shared_name_crosses_depth() {
        // g(t, {t, u})  -->  (a0, {a0, a1_1}) -> r0
        let mut t = Types::new();
        let tv = var(&mut t, 40);
        let u = var(&mut t, 41);
        let r = var(&mut t, 42);
        let tup = t.tuple(&[tv, u]);
        let g = t.address_arrow(&[tv, tup], r);

        let a0 = t.param_alpha(0);
        let a1_1 = t.address_var(&[Param(1), Field(1)]);
        let etup = t.tuple(&[a0, a1_1]);
        let r0 = t.result_alpha();
        let expected = t.arrow(&[a0, etup], r0);
        assert_eq!(g, expected, "t reuses a0 inside the tuple; u addresses to a1_1");
    }

    #[test]
    fn tagged_union_payload_variables_are_addressed_per_variant() {
        // {:cont, b} | {:halt, c} keeps b and c independent even though both
        // payloads occupy tuple field 1. Repeated b in another arm still reuses
        // b's first address through the original-variable map.
        let mut t = Types::new();
        let b = var(&mut t, 50);
        let c = var(&mut t, 51);
        let cont = {
            let tag = t.atom_lit("cont");
            t.tuple(&[tag, b])
        };
        let halt = {
            let tag = t.atom_lit("halt");
            t.tuple(&[tag, c])
        };
        let suspend = {
            let tag = t.atom_lit("suspend");
            t.tuple(&[tag, b])
        };
        let cont_or_halt = t.union(cont, halt);
        let state = t.union(cont_or_halt, suspend);
        let addressed = t.address_inputs(&[state])[0];

        let b_addr = t.address_var(&[Param(0), Variant(0), Field(1)]);
        let c_addr = t.address_var(&[Param(0), Variant(1), Field(1)]);
        assert_ne!(b_addr, c_addr, "different tagged arms must not conflate b and c");

        let cont = {
            let tag = t.atom_lit("cont");
            t.tuple(&[tag, b_addr])
        };
        let halt = {
            let tag = t.atom_lit("halt");
            t.tuple(&[tag, c_addr])
        };
        let suspend = {
            let tag = t.atom_lit("suspend");
            t.tuple(&[tag, b_addr])
        };
        let expected = {
            let two = t.union(cont, halt);
            t.union(two, suspend)
        };
        assert_eq!(addressed, expected);
    }

    #[test]
    fn address_inputs_is_idempotent_for_existing_element_addresses() {
        let mut t = Types::new();
        let head_a = t.address_var(&[Param(1), Elem]);
        let head_b = t.address_var(&[Param(1), Elem, VarSlot(0)]);
        let head = t.union(head_a, head_b);
        let list = t.non_empty_list(head);
        let scalar = t.param_alpha(0);
        let once = t.address_inputs(&[scalar, list]);
        let twice = t.address_inputs(&once);

        assert_eq!(
            twice, once,
            "re-addressing canonical list evidence must not append fresh VarSlot components"
        );
    }

    #[test]
    fn captured_values_and_nested_callable_binders_keep_scoped_correlations() {
        let mut t = Types::new();
        let shared_address = t.param_alpha(0);
        let nested = t.intern(Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args: vec![shared_address],
                ret: shared_address,
                lit: Some(ClosureLit {
                    kind: CallableValueKind::Closure,
                    fn_id: Some(ClosureTarget(7).into()),
                    captures: vec![shared_address, shared_address],
                }),
            })],
            ..Descr::none()
        });
        let closure = t.closure_lit(ClosureTarget(8), vec![shared_address, nested], 1);

        t.name_callable(ClosureTarget(7), "nested/1");
        t.name_callable(ClosureTarget(8), "outer/1");
        let root = RootId::for_test(1);
        let function = FunctionId::for_test(2);
        let key = ActivationKey::from_inputs(root, function, &[closure], &mut t);
        let once = key.inputs(&t);
        let outer_captures = t
            .closure_lit_parts(&once[0])
            .expect("addressed closure literal")
            .captures;
        assert_eq!(
            t.display(&outer_captures[0]),
            "a0_c0",
            "the prior value-surface address must be re-owned by the outer capture"
        );
        let nested_clause = t.callable_clauses(&outer_captures[1]).expect("nested callable")[0].clone();
        let nested_captures = t
            .closure_lit_parts(&outer_captures[1])
            .expect("nested closure literal")
            .captures;
        assert_eq!(
            nested_clause.args[0], shared_address,
            "the independent nested callable binder must preserve its own established address"
        );
        assert_eq!(
            nested_clause.args[0], nested_clause.ret,
            "the nested callable's arg/result correlation must survive"
        );
        assert_eq!(
            nested_captures,
            vec![nested_clause.args[0], nested_clause.args[0]],
            "repeated captures in the nested binder must reuse its callable occurrence"
        );
        assert_ne!(
            outer_captures[0], nested_clause.args[0],
            "identically spelled addresses from independent value and callable scopes must not alias"
        );

        let repeated = ActivationKey::from_inputs(root, function, &once, &mut t);
        assert_eq!(
            repeated.arrow, key.arrow,
            "re-addressing an activation key must preserve every scoped correlation exactly"
        );
    }

    #[test]
    fn generic_named_closure_capture_is_structural_and_stable_across_worlds() {
        fn relative_order(target: ClosureTarget, reverse_mint: bool) -> std::cmp::Ordering {
            let mut t = Types::new();
            if reverse_mint {
                let _ = t.float();
                let _ = t.int();
            } else {
                let _ = t.int();
                let _ = t.float();
            }
            let generic = var(&mut t, 91);
            t.name_callable(target, "pkg::map/1");
            let closure = t.closure_lit(target, vec![generic], 1);
            let activation =
                ActivationKey::from_inputs(RootId::for_test(3), FunctionId::for_test(4), &[closure], &mut t);
            let input = activation.inputs(&t)[0];
            let capture = t.closure_lit_parts(&input).expect("named closure literal").captures[0];

            assert_eq!(t.display(&capture), "a0_c0");
            assert!(
                t.free_var_ids(&activation.arrow)
                    .iter()
                    .all(|id| address_path(&t.address_paths, *id).is_some()),
                "the complete named-closure activation must contain structural addresses only"
            );
            let int = t.int();
            let ground = ActivationKey::from_inputs(RootId::for_test(3), FunctionId::for_test(4), &[int], &mut t);
            activation.semantic_cmp(&ground, &t)
        }

        assert_eq!(
            relative_order(ClosureTarget(17), false),
            relative_order(ClosureTarget(29), true),
            "callable labels and structural capture addresses, not local mint ids, own the order"
        );
    }

    #[test]
    fn capture_only_generic_is_reowned_beneath_its_literal() {
        let mut t = Types::new();
        let shared = var(&mut t, 93);
        let target = ClosureTarget(18);
        let closure = t.closure_lit(target, vec![shared], 1);

        let addressed = t.address_inputs(&[shared, closure]);
        let capture = t
            .closure_lit_parts(&addressed[1])
            .expect("addressed closure literal")
            .captures[0];

        assert_eq!(t.display(&addressed[0]), "a0");
        assert_eq!(t.display(&capture), "a1_c0");
        assert_ne!(
            addressed[0], capture,
            "a capture may share an arrow binder only through that binder's args or result"
        );
        assert_eq!(
            t.address_inputs(&addressed),
            addressed,
            "capture re-ownership must remain idempotent"
        );
    }

    #[test]
    fn sibling_and_nested_callable_binders_push_and_pop_independently() {
        fn literal_sig(types: &Types, ty: Ty, target: ClosureTarget) -> ArrowSig {
            let fn_id = target.into();
            types
                .descr(&ty)
                .funcs
                .iter()
                .flat_map(|conj| conj.pos.iter().chain(&conj.neg))
                .find(|sig| sig.lit.as_ref().is_some_and(|lit| lit.fn_id == Some(fn_id)))
                .cloned()
                .expect("literal callable clause")
        }

        let mut t = Types::new();
        let shared = var(&mut t, 92);
        let captured = t.address_var(&[Param(5)]);
        let nested_address = t.param_alpha(0);
        let nested_target = ClosureTarget(30);
        let first_target = ClosureTarget(31);
        let second_target = ClosureTarget(32);
        let nested = t.intern(Descr {
            funcs: vec![Conj::pos_of(ArrowSig {
                args: vec![nested_address],
                ret: nested_address,
                lit: Some(ClosureLit {
                    kind: CallableValueKind::Closure,
                    fn_id: Some(nested_target.into()),
                    captures: vec![nested_address],
                }),
            })],
            ..Descr::none()
        });
        let concrete = t.int();
        let siblings = t.intern(Descr {
            funcs: vec![
                Conj::pos_of(ArrowSig {
                    args: vec![shared],
                    ret: shared,
                    lit: Some(ClosureLit {
                        kind: CallableValueKind::Closure,
                        fn_id: Some(first_target.into()),
                        captures: vec![captured, shared, nested],
                    }),
                }),
                Conj::pos_of(ArrowSig {
                    args: vec![concrete, shared],
                    ret: shared,
                    lit: Some(ClosureLit {
                        kind: CallableValueKind::Closure,
                        fn_id: Some(second_target.into()),
                        captures: vec![concrete, shared, captured],
                    }),
                }),
            ],
            ..Descr::none()
        });

        let addressed = t.address_inputs(&[siblings])[0];
        let first = literal_sig(&t, addressed, first_target);
        let second = literal_sig(&t, addressed, second_target);
        let first_lit = first.lit.as_ref().expect("first literal");
        let second_lit = second.lit.as_ref().expect("second literal");
        let nested = literal_sig(&t, first_lit.captures[2], nested_target);

        assert_eq!(first.args[0], first.ret);
        assert_eq!(first.args[0], first_lit.captures[1]);
        assert_eq!(nested.args[0], nested.ret);
        assert_eq!(nested.args[0], nested.lit.as_ref().expect("nested literal").captures[0]);
        assert_eq!(second.args[1], second.ret);
        assert_eq!(second.args[1], second_lit.captures[1]);
        assert_ne!(
            first_lit.captures[0], second_lit.captures[2],
            "an established captured value must be re-owned inside each sibling binder"
        );
        assert_ne!(
            first.args[0], nested.args[0],
            "a nested binder must shadow its parent binder"
        );
        assert_eq!(
            first.args[0], second.args[1],
            "one unaddressed source generic intentionally shared across siblings must stay correlated"
        );
        assert_ne!(
            nested.args[0], second.args[1],
            "popping the nested binder must restore sibling isolation"
        );

        let repeated = t.address_inputs(&[addressed])[0];
        assert_eq!(repeated, addressed, "scoped addressing must be idempotent");
    }

    #[test]
    fn addresses_display_structurally_and_free_vars_stay_alpha() {
        // The legibility intent (fz-hwn.27.13): a canonical address renders by
        // its structural slot, while a free var renders as the bare `αN` — so
        // "is this canonical?" is answerable from the rendering alone.
        let mut t = Types::new();
        let a0 = t.param_alpha(0);
        let r0 = t.result_alpha();
        let a1_0 = t.address_var(&[Param(1), Field(0)]);
        assert_eq!(t.display(&a0), "a0");
        assert_eq!(t.display(&r0), "r0");
        assert_eq!(t.display(&a1_0), "a1_0", "a nested address renders by its path");

        let free = var(&mut t, 7);
        assert_eq!(t.display(&free), "α7", "a free var keeps the bare αN rendering");
    }

    #[test]
    fn closure_surface_vars_render_as_free_not_addresses() {
        // A closure-surface var shares the low id range with addresses
        // (`closure_var_id(fn, 0)` can equal the first address's raw index), so
        // it MUST be distinguishable: the address tag keeps it rendering `αN`,
        // never a misleading `a0` that would read as canonical.
        let mut t = Types::new();
        // Mint an address first so the low dense slot 0 is claimed by `a0`.
        let _a0 = t.param_alpha(0);
        let closure = t.fn_ref_lit(ClosureTarget(0), 1);
        let shown = t.display(&closure);
        assert!(
            shown.contains('α'),
            "closure-surface vars render as free αN, not as addresses: {shown}",
        );
        assert!(
            !shown.contains("a0"),
            "a closure-surface var must not be mistaken for the address a0: {shown}",
        );
    }

    #[test]
    fn address_tag_is_transparent_to_interning() {
        // Tagging an address id changes only its NUMBER; structurally identical
        // arrows must still fold to one interned identity, and (a, b) must still
        // differ from (a, a). The calculator reads vars by identity, never by
        // magnitude, so the tag cannot perturb equality.
        let mut t = Types::new();
        let x = var(&mut t, 100);
        let y = var(&mut t, 101);
        let int = t.int();
        let one = t.address_arrow(&[x, y], int);
        let two = t.address_arrow(&[y, x], int);
        assert_eq!(one, two, "alpha-equivalent arrows fold to one identity under tagging");
        let aa = t.address_arrow(&[x, x], int);
        assert_ne!(one, aa, "distinct params stay distinct under tagging");
    }
}
