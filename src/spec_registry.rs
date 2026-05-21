use crate::fz_ir::{FnId, SpecId};
use crate::type_vocab::TypeVarId;
use crate::types::Ty;
use std::collections::HashMap;

#[derive(Clone, Default)]
pub struct SpecRegistry {
    /// keys[spec_id.0 as usize] = (callee, input_tys).
    keys: Vec<(FnId, Vec<Ty>)>,
    /// fn_id → (input_tys → SpecId). Two-level map: outer keyed by FnId
    /// so the inner `get` can borrow `&[Ty]` via `Vec<T>: Borrow<[T]>` —
    /// zero-allocation exact-match fast path for `resolve`.
    lookup: HashMap<FnId, HashMap<Vec<Ty>, SpecId>>,
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
    pub fn register(&mut self, fn_id: FnId, input_tys: Vec<Ty>) -> SpecId {
        if let Some(&id) = self
            .lookup
            .get(&fn_id)
            .and_then(|m| m.get(input_tys.as_slice()))
        {
            return id;
        }
        let id = SpecId(self.keys.len() as u32);
        self.keys.push((fn_id, input_tys.clone()));
        self.lookup.entry(fn_id).or_default().insert(input_tys, id);
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
    pub fn register_any_key_at(&mut self, fn_id: FnId, input_tys: Vec<Ty>) -> SpecId {
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
        self.keys.push((fn_id, input_tys.clone()));
        self.lookup.entry(fn_id).or_default().insert(input_tys, id);
        self.by_fn.entry(fn_id).or_default().push(id);
        id
    }

    /// Look up the SpecId for `(fn_id, input_tys)`, or `None` if no
    /// covering spec is registered.
    ///
    /// fz-ul4.29.11 — two-tier dispatch:
    ///   1. **Fast path**: exact-match HashMap lookup. Typer and codegen
    ///      often produce identical types for the same callsite; this
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
    pub fn resolve(&self, fn_id: FnId, input_tys: &[Ty]) -> Option<SpecId> {
        use crate::types::Types;

        let t = crate::types::ConcreteTypes;
        // Fast path: zero-allocation exact match via two-level map.
        if let Some(&id) = self.lookup.get(&fn_id).and_then(|m| m.get(input_tys)) {
            return Some(id);
        }
        // Slow path: subsumption search with type-var binding.
        // fz-try.8 — each candidate is filtered via `subsumes_with` per
        // position, building a per-candidate σ. A candidate covers iff
        // every position matches AND σ is positionally consistent.
        let sids = self.by_fn.get(&fn_id)?;
        let arity = input_tys.len();
        let mut covers: Vec<SpecId> = sids
            .iter()
            .copied()
            .filter(|sid| {
                let key = &self.keys[sid.0 as usize].1;
                if key.len() != arity {
                    return false;
                }
                let mut sigma: HashMap<TypeVarId, Ty> = HashMap::new();
                input_tys
                    .iter()
                    .zip(key.iter())
                    .all(|(q, k)| t.key_subsumes_with(q, k, &mut sigma))
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
        let key_of = |sid: SpecId| -> &Vec<Ty> { &self.keys[sid.0 as usize].1 };
        let min_var_count = covers
            .iter()
            .map(|s| t.key_var_count(key_of(*s)))
            .min()
            .unwrap_or(0);
        covers.retain(|s| t.key_var_count(key_of(*s)) == min_var_count);
        let strictly_subsumed_by_other = |sid: SpecId, others: &[SpecId]| -> bool {
            let k = key_of(sid);
            others.iter().any(|&other| {
                if other == sid {
                    return false;
                }
                let ok = key_of(other);
                t.key_is_strictly_more_specific(ok, k)
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
    pub fn iter(&self) -> impl Iterator<Item = (SpecId, FnId, &[Ty])> {
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
        use crate::types::Types;

        let mut t = crate::types::ConcreteTypes;
        let key: Vec<Ty> = (0..n_params).map(|_| t.any()).collect();
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
    use crate::types::Types;

    fn fid(n: u32) -> FnId {
        FnId(n)
    }

    #[test]
    fn concrete_query_matches_var_key_with_binding() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let sid = reg.register(fid(7), vec![t.type_var(TypeVarId(0))]);
        let query = [t.int()];
        let got = reg.resolve(fid(7), &query);
        assert_eq!(got, Some(sid), "concrete query int must cover var key α");
    }

    #[test]
    fn var_query_matches_same_var_key() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let sid = reg.register(fid(7), vec![t.type_var(TypeVarId(0))]);
        let query = [t.type_var(TypeVarId(0))];
        let got = reg.resolve(fid(7), &query);
        assert_eq!(got, Some(sid), "Var α covers Var α");
    }

    #[test]
    fn var_query_matches_different_var_key_via_binding() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let sid = reg.register(fid(7), vec![t.type_var(TypeVarId(0))]);
        let query = [t.type_var(TypeVarId(5))];
        let got = reg.resolve(fid(7), &query);
        // Var β covers Var α with binding α ↦ Var β.
        assert_eq!(got, Some(sid));
    }

    #[test]
    fn var_query_does_not_match_concrete_key() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let _ = reg.register(fid(7), vec![t.int()]);
        let query = [t.type_var(TypeVarId(0))];
        let got = reg.resolve(fid(7), &query);
        // Var α NOT a subtype of int — no covering candidate.
        assert_eq!(got, None);
    }

    #[test]
    fn most_specific_wins_concrete_over_var() {
        // Both a concrete-keyed spec and a var-keyed spec cover an `int`
        // query. Dispatch must pick the concrete (most specific).
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let var_sid = reg.register(fid(7), vec![t.type_var(TypeVarId(0))]);
        let int_sid = reg.register(fid(7), vec![t.int()]);
        let query = [t.int()];
        let got = reg.resolve(fid(7), &query);
        assert_eq!(got, Some(int_sid), "concrete > var; got {:?}", got);
        assert_ne!(got, Some(var_sid), "must not return the var-form");
    }

    #[test]
    fn positionally_inconsistent_binding_fails() {
        // Key: (α, α). Query: (int, str). Single α can't bind both → no cover.
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let alpha = t.type_var(TypeVarId(0));
        let _ = reg.register(fid(7), vec![alpha.clone(), alpha]);
        let query = [t.int(), t.str_t()];
        let got = reg.resolve(fid(7), &query);
        assert_eq!(got, None, "α cannot bind to both int and str");
    }

    #[test]
    fn positionally_consistent_binding_succeeds() {
        // Key: (α, α). Query: (int, int). Single α binds to int consistently.
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let alpha = t.type_var(TypeVarId(0));
        let sid = reg.register(fid(7), vec![alpha.clone(), alpha]);
        let query = [t.int(), t.int()];
        let got = reg.resolve(fid(7), &query);
        assert_eq!(got, Some(sid));
    }

    #[test]
    fn any_query_still_does_not_match_concrete_key() {
        // Pre-fz-try.8 invariant preserved: a saturated `any` query never
        // covers a concrete key (would be unsafe — body assumes narrow inputs).
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let _ = reg.register(fid(7), vec![t.int()]);
        let query = [t.any()];
        let got = reg.resolve(fid(7), &query);
        assert_eq!(got, None);
    }
}
