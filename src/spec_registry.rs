use crate::fz_ir::{FnId, SpecId};
use std::collections::HashMap;

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
        // Slow path: subsumption search.
        let sids = self.by_fn.get(&fn_id)?;
        let arity = input_descrs.len();
        let mut covers: Vec<SpecId> = sids
            .iter()
            .copied()
            .filter(|sid| {
                let key = &self.keys[sid.0 as usize].1;
                key.len() == arity
                    && input_descrs
                        .iter()
                        .zip(key.iter())
                        .all(|(q, k)| q.is_subtype(k))
            })
            .collect();
        if covers.is_empty() {
            return None;
        }
        // Pick subtype-minimal: a candidate is "minimal" if no other
        // candidate is a strict subtype of it on every axis. Tiebreak by
        // lowest SpecId so the choice is deterministic across runs.
        let key_of = |sid: SpecId| -> &Vec<crate::types::Descr> { &self.keys[sid.0 as usize].1 };
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
                // Single-pass fold: require all ok[i] ⊆ k[i] and at least
                // one strictly so (i.e. k[i] ⊄ ok[i]).
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
        // Mutually subtype-equivalent set — pick lowest SpecId.
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
