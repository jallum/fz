use crate::fz_ir::{FnId, SpecId};
use crate::types::{Descr, TypeVarId};
use std::collections::HashMap;

/// fz-try.8 — subsumption-with-type-var-binding at a single key position.
/// Implements the truth table in `docs/descr-cleanup.md`:
///
/// | q        | k        | result | binding produced |
/// |----------|----------|--------|------------------|
/// | Any      | Any      | yes    | none             |
/// | Concrete | Any      | yes    | none             |
/// | Var α    | Any      | yes    | none             |
/// | Concrete | Concrete | iff q ⊆ k | none          |
/// | Concrete | Var α    | yes    | α ↦ Concrete     |
/// | Var α    | Var α    | yes    | none             |
/// | Var α    | Var β    | yes    | α ↦ Var β        |
/// | Var α    | Concrete | no     | —                |
/// | Any      | Concrete | no     | —                |
/// | Any      | Var α    | no     | —                |
///
/// Mutates `sigma` with any new binding; returns `false` if a binding
/// would conflict with an existing one (positionally inconsistent
/// instantiation — the candidate fails to cover).
///
/// "Pure-var" means a Descr whose only non-empty axis is the top-level
/// `vars` set. Structural vars (vars inside arrows/tuples/lists/maps)
/// are not bound here — the lattice's structural is_subtype handles
/// those once positionally outer vars are bound. This matches the
/// design's "monomorphize per call, no recursive unification."
fn subsumes_with(q: &Descr, k: &Descr, sigma: &mut HashMap<TypeVarId, Descr>) -> bool {
    let k_is_any = k.looks_full();
    if k_is_any {
        return true;
    }
    if let Some(alphas) = pure_var_ids(k) {
        // k carries one (or more) named var ids and nothing else. Bind each
        // to the witness q; check consistency with existing σ.
        // For single-var keys (overwhelming majority), this is one binding.
        for alpha in alphas {
            match sigma.get(&alpha) {
                None => {
                    sigma.insert(alpha, q.clone());
                }
                Some(existing) => {
                    if !existing.is_equiv(q) {
                        return false; // positionally inconsistent
                    }
                }
            }
        }
        return true;
    }
    // k is concrete (no named vars at the top level). q must structurally
    // subtype k. The lattice's is_subtype already handles this — including
    // q-has-vars-vs-k-concrete, which produces false because vars are
    // disjoint from concrete axes.
    q.is_subtype(k)
}

/// If `d` is a "pure var" descriptor — carrying named type vars on the
/// vars axis and nothing else (no basic/atoms/ints/floats/strs/opaques/
/// tuples/lists/funcs/maps) — return the finite list of var ids. Else
/// None. Cofinite-vars (e.g. `Descr::any()`'s vars axis = "every var")
/// is NOT pure-var, because σ can't bind "every var" to a witness.
fn pure_var_ids(d: &Descr) -> Option<Vec<TypeVarId>> {
    let mut comps = d.components();
    let only = comps.next()?;
    if comps.next().is_some() {
        return None;
    }
    match only {
        crate::types::Component::Vars(view) => {
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

/// Count of named type vars at the top level of `key`. Used by the
/// most-specific-wins ordering: fewer named vars = more concrete = more
/// specific. The Castagna set-theoretic order says concrete > some-Var >
/// all-Var; this count is the proxy.
fn key_var_count(key: &[Descr]) -> usize {
    key.iter()
        .map(|d| {
            d.components()
                .filter_map(|c| match c {
                    crate::types::Component::Vars(v) => v.finite_len(),
                    _ => None,
                })
                .sum::<usize>()
        })
        .sum()
}

#[derive(Clone, Default)]
pub struct SpecRegistry {
    /// keys[spec_id.0 as usize] = (callee, input_descrs).
    keys: Vec<(FnId, Vec<crate::types::Descr>)>,
    /// fn_id → (input_descrs → SpecId). Two-level map: outer keyed by FnId
    /// so the inner `get` can borrow `&[Descr]` via `Vec<T>: Borrow<[T]>` —
    /// zero-allocation exact-match fast path for `resolve`.
    lookup: HashMap<FnId, HashMap<Vec<crate::types::Descr>, SpecId>>,
    /// fz-ul4.29.11 — per-FnId list of registered SpecIds, used by the
    /// subsumption fallback in `resolve`. Excludes sentinel slots inserted
    /// by `register_any_key_at`'s padding (those have no real registration).
    by_fn: HashMap<FnId, Vec<SpecId>>,
}

impl SpecRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a `(fn_id, input_descrs)` pair; return its SpecId. If
    /// already registered, returns the existing SpecId without
    /// duplicating.
    pub fn register(&mut self, fn_id: FnId, input_descrs: Vec<crate::types::Descr>) -> SpecId {
        if let Some(&id) = self
            .lookup
            .get(&fn_id)
            .and_then(|m| m.get(input_descrs.as_slice()))
        {
            return id;
        }
        let id = SpecId(self.keys.len() as u32);
        self.keys.push((fn_id, input_descrs.clone()));
        self.lookup
            .entry(fn_id)
            .or_default()
            .insert(input_descrs, id);
        self.by_fn.entry(fn_id).or_default().push(id);
        id
    }

    /// Register an any-key spec so that its SpecId.0 equals `fn_id.0`.
    /// Pads with dead sentinel slots for any intervening missing FnIds
    /// (cps_split may have produced sparse FnId.0 values when fns get
    /// dropped or reordered). Sentinel slots are filled with the same
    /// (fn_id, key) so `iter()` is well-shaped — they're never reached
    /// because their fn_id doesn't appear in the module. Callers must
    /// register any-keys in FnId.0 order.
    pub fn register_any_key_at(
        &mut self,
        fn_id: FnId,
        input_descrs: Vec<crate::types::Descr>,
    ) -> SpecId {
        let target = fn_id.0 as usize;
        while self.keys.len() < target {
            // Sentinel: tag with the slot's FnId so iter() reports a
            // self-consistent (SpecId, FnId, key) tuple; this slot's
            // FnId doesn't exist in the module, so the slot is dead.
            let sentinel_fn = FnId(self.keys.len() as u32);
            let sentinel_key = (sentinel_fn, Vec::new());
            self.keys.push(sentinel_key);
            // No `lookup` entry — the slot is unreachable from resolve().
        }
        let id = SpecId(self.keys.len() as u32);
        debug_assert_eq!(id.0, fn_id.0);
        self.keys.push((fn_id, input_descrs.clone()));
        self.lookup
            .entry(fn_id)
            .or_default()
            .insert(input_descrs, id);
        self.by_fn.entry(fn_id).or_default().push(id);
        id
    }

    /// Look up the SpecId for `(fn_id, input_descrs)`, or `None` if no
    /// covering spec is registered.
    ///
    /// fz-ul4.29.11 — two-tier dispatch:
    ///   1. **Fast path**: exact-match HashMap lookup. Typer and codegen
    ///      often produce identical Descrs for the same callsite; this
    ///      path covers that common case in O(1).
    ///   2. **Slow path**: subsumption search over per-FnId specs. A
    ///      registered spec covers a query iff `query[i] ⊆ key[i]` for
    ///      every element (the spec's body was compiled assuming inputs
    ///      of type `key`, so a narrower query is safe to dispatch to it).
    ///      Among covering candidates, picks the subtype-minimal one —
    ///      the most-specialized safe dispatch. Deterministic SpecId
    ///      tiebreak when candidates are subtype-incomparable.
    ///
    /// Best-match specialization quality (typer registering tight-enough
    /// specs at every callsite) is a separate concern — different ticket.
    pub fn resolve(&self, fn_id: FnId, input_descrs: &[crate::types::Descr]) -> Option<SpecId> {
        // Fast path: zero-allocation exact match via two-level map.
        if let Some(&id) = self.lookup.get(&fn_id).and_then(|m| m.get(input_descrs)) {
            return Some(id);
        }
        // Slow path: subsumption search with type-var binding.
        // fz-try.8 — each candidate is filtered via `subsumes_with` per
        // position, building a per-candidate σ. A candidate covers iff
        // every position matches AND σ is positionally consistent.
        let sids = self.by_fn.get(&fn_id)?;
        let arity = input_descrs.len();
        let mut covers: Vec<SpecId> = sids
            .iter()
            .copied()
            .filter(|sid| {
                let key = &self.keys[sid.0 as usize].1;
                if key.len() != arity {
                    return false;
                }
                let mut sigma: HashMap<TypeVarId, Descr> = HashMap::new();
                input_descrs
                    .iter()
                    .zip(key.iter())
                    .all(|(q, k)| subsumes_with(q, k, &mut sigma))
            })
            .collect();
        if covers.is_empty() {
            return None;
        }
        // Most-specific-wins ordering (Castagna set-theoretic order):
        // concrete > some-Var > all-Var. The proxy is named-var count at
        // the top level — fewer vars in the key = more specific.
        //
        // Within the same var-count tier, fall back to lattice subsumption
        // (a candidate is "minimal" if no other candidate is a strict
        // subtype on every axis), then SpecId for stable tiebreak.
        let key_of = |sid: SpecId| -> &Vec<Descr> { &self.keys[sid.0 as usize].1 };
        let min_var_count = covers
            .iter()
            .map(|s| key_var_count(key_of(*s)))
            .min()
            .unwrap_or(0);
        covers.retain(|s| key_var_count(key_of(*s)) == min_var_count);
        let strictly_subsumed_by_other = |sid: SpecId, others: &[SpecId]| -> bool {
            let k = key_of(sid);
            others.iter().any(|&other| {
                if other == sid {
                    return false;
                }
                let ok = key_of(other);
                if ok.len() != k.len() {
                    return false;
                }
                ok.iter()
                    .zip(k.iter())
                    .fold((true, false), |(all_le, any_strict), (o, kk)| {
                        (all_le && o.is_subtype(kk), any_strict || !kk.is_subtype(o))
                    })
                    == (true, true)
            })
        };
        covers.sort_by_key(|s| s.0);
        for sid in &covers {
            if !strictly_subsumed_by_other(*sid, &covers) {
                return Some(*sid);
            }
        }
        covers.into_iter().min_by_key(|s| s.0)
    }

    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Iterate all `(SpecId, &FnId, &input_descrs)` entries in SpecId
    /// order. Used by the codegen pipeline to walk every compiled body.
    pub fn iter(&self) -> impl Iterator<Item = (SpecId, FnId, &[crate::types::Descr])> {
        self.keys
            .iter()
            .enumerate()
            .map(|(i, (f, d))| (SpecId(i as u32), *f, d.as_slice()))
    }
}

#[cfg(test)]
impl SpecRegistry {
    /// Look up a fn's any-key SpecId. Test-only helper.
    pub fn any_key(&self, fn_id: FnId, n_params: usize) -> SpecId {
        let key = vec![crate::types::Descr::any(); n_params];
        *self
            .lookup
            .get(&fn_id)
            .and_then(|m| m.get(key.as_slice()))
            .expect("any-key spec must always be registered for every fn")
    }
}

// ----------------------------------------------------------------------
// fz-try.8 — subsumption-with-vars tests
// ----------------------------------------------------------------------

#[cfg(test)]
mod var_subsumption_tests {
    use super::*;
    use crate::types::Descr;

    fn fid(n: u32) -> FnId {
        FnId(n)
    }

    #[test]
    fn concrete_query_matches_var_key_with_binding() {
        let mut reg = SpecRegistry::new();
        let sid = reg.register(fid(7), vec![Descr::var(TypeVarId(0))]);
        let got = reg.resolve(fid(7), &[Descr::int()]);
        assert_eq!(got, Some(sid), "concrete query int must cover var key α");
    }

    #[test]
    fn var_query_matches_same_var_key() {
        let mut reg = SpecRegistry::new();
        let sid = reg.register(fid(7), vec![Descr::var(TypeVarId(0))]);
        let got = reg.resolve(fid(7), &[Descr::var(TypeVarId(0))]);
        assert_eq!(got, Some(sid), "Var α covers Var α");
    }

    #[test]
    fn var_query_matches_different_var_key_via_binding() {
        let mut reg = SpecRegistry::new();
        let sid = reg.register(fid(7), vec![Descr::var(TypeVarId(0))]);
        let got = reg.resolve(fid(7), &[Descr::var(TypeVarId(5))]);
        // Var β covers Var α with binding α ↦ Var β.
        assert_eq!(got, Some(sid));
    }

    #[test]
    fn var_query_does_not_match_concrete_key() {
        let mut reg = SpecRegistry::new();
        let _ = reg.register(fid(7), vec![Descr::int()]);
        let got = reg.resolve(fid(7), &[Descr::var(TypeVarId(0))]);
        // Var α NOT a subtype of int — no covering candidate.
        assert_eq!(got, None);
    }

    #[test]
    fn most_specific_wins_concrete_over_var() {
        // Both a concrete-keyed spec and a var-keyed spec cover an `int`
        // query. Dispatch must pick the concrete (most specific).
        let mut reg = SpecRegistry::new();
        let var_sid = reg.register(fid(7), vec![Descr::var(TypeVarId(0))]);
        let int_sid = reg.register(fid(7), vec![Descr::int()]);
        let got = reg.resolve(fid(7), &[Descr::int()]);
        assert_eq!(got, Some(int_sid), "concrete > var; got {:?}", got);
        assert_ne!(got, Some(var_sid), "must not return the var-form");
    }

    #[test]
    fn positionally_inconsistent_binding_fails() {
        // Key: (α, α). Query: (int, str). Single α can't bind both → no cover.
        let mut reg = SpecRegistry::new();
        let _ = reg.register(
            fid(7),
            vec![Descr::var(TypeVarId(0)), Descr::var(TypeVarId(0))],
        );
        let got = reg.resolve(fid(7), &[Descr::int(), Descr::str_t()]);
        assert_eq!(got, None, "α cannot bind to both int and str");
    }

    #[test]
    fn positionally_consistent_binding_succeeds() {
        // Key: (α, α). Query: (int, int). Single α binds to int consistently.
        let mut reg = SpecRegistry::new();
        let sid = reg.register(
            fid(7),
            vec![Descr::var(TypeVarId(0)), Descr::var(TypeVarId(0))],
        );
        let got = reg.resolve(fid(7), &[Descr::int(), Descr::int()]);
        assert_eq!(got, Some(sid));
    }

    #[test]
    fn any_query_still_does_not_match_concrete_key() {
        // Pre-fz-try.8 invariant preserved: a saturated `any` query never
        // covers a concrete key (would be unsafe — body assumes narrow inputs).
        let mut reg = SpecRegistry::new();
        let _ = reg.register(fid(7), vec![Descr::int()]);
        let got = reg.resolve(fid(7), &[Descr::any()]);
        assert_eq!(got, None);
    }

    #[test]
    fn pure_var_helper_discriminates_correctly() {
        assert!(pure_var_ids(&Descr::var(TypeVarId(0))).is_some());
        assert!(pure_var_ids(&Descr::int()).is_none());
        // `Descr::any()` is cofinite on vars (every var) — not substitutable.
        assert!(pure_var_ids(&Descr::any()).is_none());
        assert!(pure_var_ids(&Descr::none()).is_none());
        // int ∪ Var(α) is concrete-with-vars; NOT pure-var.
        let mixed = Descr::int().union(&Descr::var(TypeVarId(0)));
        assert!(pure_var_ids(&mixed).is_none());
    }
}
