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
//! adding a field never renumbers `d`. This is what
//! [`Types::alpha_normalize_vars`] cannot express: it numbers by encounter
//! order, so `d` would be `a3` and would drift when the tuple grows.
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
use super::lit_set::LiteralSet;
use super::{Ty, TypeVarId, Types};

/// One step of a structural address. A full address is a `&[AddrStep]` path
/// rooted at a parameter or the result slot.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AddrStep {
    /// Parameter `i` of the arrow (top level).
    Param(u16),
    /// The arrow's result slot.
    Result,
    /// Field `j` of the tuple at the current address.
    Field(u16),
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

impl Types {
    /// Intern a structural address to its canonical [`TypeVarId`]. Same address
    /// always yields the same id, so `param_alpha(0)` is stable across every
    /// signature built by this `Types` instance.
    pub fn address_id(&mut self, path: &[AddrStep]) -> TypeVarId {
        if let Some(&id) = self.address_vars.get(path) {
            return id;
        }
        let id = TypeVarId(self.address_vars.len() as u32);
        self.address_vars.insert(path.to_vec(), id);
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

    /// `r0` — the variable at the result slot.
    pub fn result_alpha(&mut self) -> Ty {
        self.address_var(&[AddrStep::Result])
    }

    /// Build the canonical addressed arrow for a signature. Each original
    /// variable is mapped to the address of its first occurrence (pre-order:
    /// `params[0..]` depth-first, then `result`); repeats reuse that address.
    /// Concrete structure (tuples, lists, brands, refinements) is preserved
    /// exactly — only variable identity is canonicalized.
    pub fn address_arrow(&mut self, params: &[Ty], result: Ty) -> Ty {
        let mut map: HashMap<TypeVarId, TypeVarId> = HashMap::new();
        let params: Vec<Ty> = params
            .iter()
            .enumerate()
            .map(|(i, &p)| self.address_remap(p, &[AddrStep::Param(i as u16)], &mut map))
            .collect();
        let result = self.address_remap(result, &[AddrStep::Result], &mut map);
        self.arrow(&params, result)
    }

    /// Rewrite every variable in `ty` to its first-occurrence address, threading
    /// `map` (original id -> address id) so repeated variables share, and
    /// recursing into nested shapes with the address path extended.
    fn address_remap(&mut self, ty: Ty, path: &[AddrStep], map: &mut HashMap<TypeVarId, TypeVarId>) -> Ty {
        if !self.has_vars(&ty) {
            return ty;
        }
        let mut d = self.descr(&ty).clone();
        if !d.vars.cofinite && !d.vars.set.is_empty() {
            d.vars = self.address_vars_at(&d.vars, path, map);
        }
        self.address_remap_children(&mut d, path, map);
        self.intern(d)
    }

    /// Map the finite variable set living at one node to address ids. A single
    /// variable takes the node's address; a union of several takes `VarSlot(k)`
    /// sub-addresses so distinct variables never collide.
    fn address_vars_at(
        &mut self,
        vars: &LiteralSet<TypeVarId>,
        path: &[AddrStep],
        map: &mut HashMap<TypeVarId, TypeVarId>,
    ) -> LiteralSet<TypeVarId> {
        let originals: Vec<TypeVarId> = vars.set.iter().copied().collect();
        let single = originals.len() == 1;
        let mut set = BTreeSet::new();
        for (k, original) in originals.into_iter().enumerate() {
            let mapped = match map.get(&original) {
                Some(&id) => id,
                None => {
                    let id = if single {
                        self.address_id(path)
                    } else {
                        let mut child = path.to_vec();
                        child.push(AddrStep::VarSlot(k as u16));
                        self.address_id(&child)
                    };
                    map.insert(original, id);
                    id
                }
            };
            set.insert(mapped);
        }
        LiteralSet { set, cofinite: false }
    }

    /// Recurse into the nested shapes of `d`, extending the address path by the
    /// structural step at each child (mirrors `map_recursive_inputs_with`, but
    /// path-aware).
    fn address_remap_children(&mut self, d: &mut Descr, path: &[AddrStep], map: &mut HashMap<TypeVarId, TypeVarId>) {
        for conj in &mut d.tuples {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                for (j, ty) in sig.elems.iter_mut().enumerate() {
                    let mut child = path.to_vec();
                    child.push(AddrStep::Field(j as u16));
                    *ty = self.address_remap(*ty, &child, map);
                }
            }
        }
        for conj in &mut d.lists {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                if let Some(elem) = sig.elem {
                    let mut child = path.to_vec();
                    child.push(AddrStep::Elem);
                    sig.elem = Some(self.address_remap(elem, &child, map));
                }
            }
        }
        for conj in &mut d.resources {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                let mut child = path.to_vec();
                child.push(AddrStep::Payload);
                sig.payload = self.address_remap(sig.payload, &child, map);
            }
        }
        for conj in &mut d.funcs {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                for (i, ty) in sig.args.iter_mut().enumerate() {
                    let mut child = path.to_vec();
                    child.push(AddrStep::Param(i as u16));
                    *ty = self.address_remap(*ty, &child, map);
                }
                let mut child = path.to_vec();
                child.push(AddrStep::Result);
                sig.ret = self.address_remap(sig.ret, &child, map);
            }
        }
        for conj in &mut d.maps {
            for sig in conj.pos.iter_mut().chain(conj.neg.iter_mut()) {
                for (j, (_, ty)) in sig.fields.iter_mut().enumerate() {
                    let mut child = path.to_vec();
                    child.push(AddrStep::MapField(j as u16));
                    *ty = self.address_remap(*ty, &child, map);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::AddrStep::{Field, Param};
    use super::*;

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
}
