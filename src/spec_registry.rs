use crate::fz_ir::{FnId, SpecId};
use crate::types::{Ty, TypeVarId};
use std::collections::HashMap;

#[derive(Clone)]
struct SpecEntry {
    fn_id: FnId,
    key: Vec<Ty>,
    key_var_count: usize,
    precedence: u32,
    is_registered: bool,
}

#[derive(Clone, Default)]
struct SpecFamily {
    /// Exact-match fast path for this callee family.
    exact: HashMap<Vec<Ty>, SpecId>,
    /// Registered spec ids for this callee in stable precedence order.
    ordered: Vec<SpecId>,
}

#[derive(Clone, Copy)]
pub(crate) struct BestCoverCandidate<'a, Id> {
    pub id: Id,
    pub key: &'a [Ty],
    pub key_var_count: usize,
    pub precedence: u32,
}

pub(crate) fn best_covering_candidate<'a, T, Id>(
    t: &T,
    query: &[Ty],
    candidates: impl IntoIterator<Item = BestCoverCandidate<'a, Id>>,
) -> Option<Id>
where
    T: crate::types::Types<Ty = crate::types::Ty>,
    Id: Copy + Eq,
{
    let arity = query.len();
    let mut covers: Vec<BestCoverCandidate<'a, Id>> = candidates
        .into_iter()
        .filter(|candidate| {
            if candidate.key.len() != arity {
                return false;
            }
            let mut sigma: HashMap<TypeVarId, Ty> = HashMap::new();
            query
                .iter()
                .zip(candidate.key.iter())
                .all(|(q, k)| t.key_subsumes_with(q, k, &mut sigma))
        })
        .collect();
    if covers.is_empty() {
        return None;
    }
    let min_var_count = covers
        .iter()
        .map(|candidate| candidate.key_var_count)
        .min()
        .unwrap_or(0);
    covers.retain(|candidate| candidate.key_var_count == min_var_count);
    covers.sort_by_key(|candidate| candidate.precedence);
    for candidate in &covers {
        let strictly_subsumed_by_other = covers.iter().any(|other| {
            other.id != candidate.id && t.key_is_strictly_more_specific(other.key, candidate.key)
        });
        if !strictly_subsumed_by_other {
            return Some(candidate.id);
        }
    }
    covers.first().map(|candidate| candidate.id)
}

#[derive(Clone, Default)]
pub struct SpecRegistry {
    /// entries[spec_id.0 as usize] = specialization metadata. Sentinel
    /// slots inserted by `register_any_key_at` remain present so the
    /// `SpecId.0 == FnId.0` any-key invariant is preserved.
    entries: Vec<SpecEntry>,
    /// Per-callee specialization families. Each family owns the exact
    /// lookup table and the ordered registered candidates for slow-path
    /// cover selection. Sentinel slots never appear here.
    families: HashMap<FnId, SpecFamily>,
}

impl SpecRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    fn key_var_count_for(key: &[Ty]) -> usize {
        use crate::types::Types;

        let t = crate::types::ConcreteTypes;
        t.key_var_count(key)
    }

    fn entry(&self, sid: SpecId) -> &SpecEntry {
        &self.entries[sid.0 as usize]
    }

    fn exact_match(&self, fn_id: FnId, input_tys: &[Ty]) -> Option<SpecId> {
        self.families
            .get(&fn_id)
            .and_then(|f| f.exact.get(input_tys))
            .copied()
    }

    fn push_sentinel(&mut self, fn_id: FnId) {
        self.entries.push(SpecEntry {
            fn_id,
            key: Vec::new(),
            key_var_count: 0,
            precedence: 0,
            is_registered: false,
        });
    }

    #[cfg(test)]
    fn next_precedence(&self, fn_id: FnId) -> u32 {
        self.families
            .get(&fn_id)
            .map(|family| family.ordered.len() as u32)
            .unwrap_or(0)
    }

    fn register_entry_with_precedence(
        &mut self,
        fn_id: FnId,
        input_tys: Vec<Ty>,
        precedence: u32,
    ) -> SpecId {
        let id = SpecId(self.entries.len() as u32);
        let key_var_count = Self::key_var_count_for(&input_tys);
        self.entries.push(SpecEntry {
            fn_id,
            key: input_tys.clone(),
            key_var_count,
            precedence,
            is_registered: true,
        });
        let family = self.families.entry(fn_id).or_default();
        family.exact.insert(input_tys, id);
        family.ordered.push(id);
        id
    }

    /// Register a `(fn_id, input_descrs)` pair; return its SpecId. If
    /// already registered, returns the existing SpecId without
    /// duplicating.
    #[cfg(test)]
    pub fn register(&mut self, fn_id: FnId, input_tys: Vec<Ty>) -> SpecId {
        let precedence = self.next_precedence(fn_id);
        self.register_with_precedence(fn_id, input_tys, precedence)
    }

    pub fn register_with_precedence(
        &mut self,
        fn_id: FnId,
        input_tys: Vec<Ty>,
        precedence: u32,
    ) -> SpecId {
        if let Some(id) = self.exact_match(fn_id, input_tys.as_slice()) {
            return id;
        }
        self.register_entry_with_precedence(fn_id, input_tys, precedence)
    }

    /// Register an any-key spec so that its SpecId.0 equals `fn_id.0`.
    /// Pads with dead sentinel slots for any intervening missing FnIds
    /// (cps_split may have produced sparse FnId.0 values when fns get
    /// dropped or reordered). Sentinel slots are filled with the same
    /// (fn_id, key) so `iter()` is well-shaped — they're never reached
    /// because their fn_id doesn't appear in the module. Callers must
    /// register any-keys in FnId.0 order.
    pub fn register_any_key_at_with_precedence(
        &mut self,
        fn_id: FnId,
        input_tys: Vec<Ty>,
        precedence: u32,
    ) -> SpecId {
        let target = fn_id.0 as usize;
        while self.entries.len() < target {
            // Sentinel: tag with the slot's FnId so iter() reports a
            // self-consistent (SpecId, FnId, key) tuple; this slot's
            // FnId doesn't exist in the module, so the slot is dead.
            let sentinel_fn = FnId(self.entries.len() as u32);
            self.push_sentinel(sentinel_fn);
        }
        let id = SpecId(self.entries.len() as u32);
        debug_assert_eq!(id.0, fn_id.0);
        self.register_entry_with_precedence(fn_id, input_tys, precedence)
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
    ///      the most-specialized safe dispatch. Stable family
    ///      precedence breaks ties when candidates are
    ///      subtype-incomparable.
    ///
    /// Best-match specialization quality (typer registering tight-enough
    /// specs at every callsite) is a separate concern — different ticket.
    pub fn resolve(&self, fn_id: FnId, input_tys: &[Ty]) -> Option<SpecId> {
        let t = crate::types::ConcreteTypes;
        // Fast path: zero-allocation exact match via per-family lookup.
        if let Some(id) = self.exact_match(fn_id, input_tys) {
            return Some(id);
        }
        let family = self.families.get(&fn_id)?;
        best_covering_candidate(
            &t,
            input_tys,
            family.ordered.iter().copied().map(|sid| {
                let entry = self.entry(sid);
                debug_assert!(entry.is_registered);
                BestCoverCandidate {
                    id: sid,
                    key: entry.key.as_slice(),
                    key_var_count: entry.key_var_count,
                    precedence: entry.precedence,
                }
            }),
        )
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Iterate all `(SpecId, &FnId, &input_descrs)` entries in SpecId
    /// order. Used by the codegen pipeline to walk every compiled body.
    pub fn iter(&self) -> impl Iterator<Item = (SpecId, FnId, &[Ty])> {
        self.entries
            .iter()
            .enumerate()
            .map(|(i, entry)| (SpecId(i as u32), entry.fn_id, entry.key.as_slice()))
    }
}

#[cfg(test)]
impl SpecRegistry {
    /// Look up a fn's any-key SpecId. Test-only helper.
    pub fn any_key(&self, fn_id: FnId, n_params: usize) -> SpecId {
        use crate::types::Types;

        let mut t = crate::types::ConcreteTypes;
        let key: Vec<Ty> = (0..n_params).map(|_| t.any()).collect();
        self.exact_match(fn_id, key.as_slice())
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
