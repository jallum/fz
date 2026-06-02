use crate::fz_ir::{FnId, SpecId};
use crate::ir_planner::fn_types::{ReturnDemand, SpecKey};
use crate::types::{KeySlot, Ty, TypeVarId, key_slot_var_count};
use std::collections::HashMap;

#[derive(Clone)]
struct SpecEntry {
    key: SpecKey,
    key_var_count: usize,
    precedence: u32,
    is_registered: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SpecFamilyId {
    fn_id: FnId,
    demand: ReturnDemand,
}

impl From<&SpecKey> for SpecFamilyId {
    fn from(key: &SpecKey) -> Self {
        Self {
            fn_id: key.fn_id,
            demand: key.demand.clone(),
        }
    }
}

#[derive(Clone, Default)]
struct SpecFamily {
    /// Exact-match fast path for this callee family.
    exact: HashMap<Vec<KeySlot>, SpecId>,
    /// Registered spec ids for this callee in stable precedence order.
    ordered: Vec<SpecId>,
}

#[derive(Clone, Copy)]
pub(crate) struct BestCoverCandidate<'a, Id> {
    pub id: Id,
    pub key: &'a [KeySlot],
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
                .all(|(q, k)| match k {
                    None => true,
                    Some(k) => t.key_subsumes_with(q, k, &mut sigma),
                })
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
            other.id != candidate.id
                && key_slots_strictly_more_specific(t, other.key, candidate.key)
        });
        if !strictly_subsumed_by_other {
            return Some(candidate.id);
        }
    }
    covers.first().map(|candidate| candidate.id)
}

fn key_slots_strictly_more_specific<T>(t: &T, a: &[KeySlot], b: &[KeySlot]) -> bool
where
    T: crate::types::Types<Ty = crate::types::Ty>,
{
    if a.len() != b.len() {
        return false;
    }
    let mut aa = Vec::new();
    let mut bb = Vec::new();
    for (a_slot, b_slot) in a.iter().zip(b.iter()) {
        match (a_slot, b_slot) {
            (None, None) => {}
            (Some(a_ty), Some(b_ty)) => {
                aa.push(a_ty.clone());
                bb.push(b_ty.clone());
            }
            _ => return false,
        }
    }
    t.key_is_strictly_more_specific(&aa, &bb)
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
    families: HashMap<SpecFamilyId, SpecFamily>,
}

impl SpecRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    fn entry(&self, sid: SpecId) -> &SpecEntry {
        &self.entries[sid.0 as usize]
    }

    #[cfg(test)]
    fn exact_match(&self, fn_id: FnId, input_tys: &[KeySlot]) -> Option<SpecId> {
        self.exact_match_spec_key(&SpecKey::value(fn_id, input_tys.to_vec()))
    }

    fn exact_match_spec_key(&self, key: &SpecKey) -> Option<SpecId> {
        self.families
            .get(&SpecFamilyId::from(key))
            .and_then(|f| f.exact.get(&key.input))
            .copied()
    }

    fn push_sentinel(&mut self, fn_id: FnId) {
        self.entries.push(SpecEntry {
            key: SpecKey::value(fn_id, Vec::new()),
            key_var_count: 0,
            precedence: 0,
            is_registered: false,
        });
    }

    #[cfg(test)]
    fn next_precedence(&self, fn_id: FnId) -> u32 {
        self.families
            .get(&SpecFamilyId {
                fn_id,
                demand: ReturnDemand::value(),
            })
            .map(|family| family.ordered.len() as u32)
            .unwrap_or(0)
    }

    fn register_entry_with_precedence(
        &mut self,
        t: &impl crate::types::Types<Ty = crate::types::Ty>,
        key: SpecKey,
        precedence: u32,
    ) -> SpecId {
        let id = SpecId(self.entries.len() as u32);
        let key_var_count = key_slot_var_count(t, &key.input);
        self.entries.push(SpecEntry {
            key: key.clone(),
            key_var_count,
            precedence,
            is_registered: true,
        });
        let family = self.families.entry(SpecFamilyId::from(&key)).or_default();
        family.exact.insert(key.input, id);
        family.ordered.push(id);
        id
    }

    /// Register a `(fn_id, input_descrs)` pair; return its SpecId. If
    /// already registered, returns the existing SpecId without
    /// duplicating.
    #[cfg(test)]
    pub fn register<K: Into<KeySlot>>(
        &mut self,
        t: &impl crate::types::Types<Ty = crate::types::Ty>,
        fn_id: FnId,
        input_tys: Vec<K>,
    ) -> SpecId {
        let precedence = self.next_precedence(fn_id);
        self.register_with_precedence(t, fn_id, input_tys, precedence)
    }

    pub fn register_spec_key_with_precedence(
        &mut self,
        t: &impl crate::types::Types<Ty = crate::types::Ty>,
        key: SpecKey,
        precedence: u32,
    ) -> SpecId {
        if let Some(id) = self.exact_match_spec_key(&key) {
            return id;
        }
        self.register_entry_with_precedence(t, key, precedence)
    }

    #[cfg(test)]
    pub fn register_with_precedence<K: Into<KeySlot>>(
        &mut self,
        t: &impl crate::types::Types<Ty = crate::types::Ty>,
        fn_id: FnId,
        input_tys: Vec<K>,
        precedence: u32,
    ) -> SpecId {
        let input_tys: Vec<KeySlot> = input_tys.into_iter().map(Into::into).collect();
        self.register_spec_key_with_precedence(t, SpecKey::value(fn_id, input_tys), precedence)
    }

    /// Register an any-key spec so that its SpecId.0 equals `fn_id.0`.
    /// Pads with dead sentinel slots for any intervening missing FnIds
    /// (cps_split may have produced sparse FnId.0 values when fns get
    /// dropped or reordered). Sentinel slots are filled with the same
    /// (fn_id, key) so `iter()` is well-shaped — they're never reached
    /// because their fn_id doesn't appear in the module. Callers must
    /// register any-keys in FnId.0 order.
    pub fn register_any_key_at_with_precedence<K: Into<KeySlot>>(
        &mut self,
        t: &impl crate::types::Types<Ty = crate::types::Ty>,
        fn_id: FnId,
        input_tys: Vec<K>,
        precedence: u32,
    ) -> SpecId {
        let input_tys: Vec<KeySlot> = input_tys.into_iter().map(Into::into).collect();
        let key = SpecKey::value(fn_id, input_tys);
        self.register_spec_key_at_with_precedence(t, key, precedence)
    }

    pub fn register_spec_key_at_with_precedence(
        &mut self,
        t: &impl crate::types::Types<Ty = crate::types::Ty>,
        key: SpecKey,
        precedence: u32,
    ) -> SpecId {
        debug_assert_eq!(
            key.demand,
            ReturnDemand::value(),
            "SpecId.0 == FnId.0 any-key slots are a value-entry ABI"
        );
        let fn_id = key.fn_id;
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
        self.register_entry_with_precedence(t, key, precedence)
    }

    /// Look up the SpecId for `(fn_id, input_tys)`, or `None` if no
    /// covering spec is registered.
    ///
    /// fz-ul4.29.11 — two-tier dispatch:
    ///   1. **Fast path**: exact-match HashMap lookup. Planner and codegen
    ///      often produce identical types for the same callsite; this
    ///      path covers that common case in O(1).
    ///   2. **Slow path**: subsumption search over per-FnId specs. A
    ///      registered spec covers a query iff `query[i] ⊆ key[i]` for
    ///      every typed element. `None` key slots are positional holes:
    ///      they preserve arity and are skipped, never treated as `any`.
    ///      The spec's body was compiled assuming inputs of type `key`, so
    ///      a narrower query is safe to dispatch to it.
    ///      Among covering candidates, picks the subtype-minimal one —
    ///      the most-specialized safe dispatch. Stable family
    ///      precedence breaks ties when candidates are
    ///      subtype-incomparable.
    ///
    /// Best-match specialization quality (planner registering tight-enough
    /// specs at every callsite) is a separate concern — different ticket.
    #[cfg(test)]
    pub fn resolve(
        &self,
        t: &impl crate::types::Types<Ty = crate::types::Ty>,
        fn_id: FnId,
        input_tys: &[Ty],
    ) -> Option<SpecId> {
        let input_key = crate::types::key_slots_from_tys(input_tys.iter().cloned());
        self.resolve_spec_key(t, &SpecKey::value(fn_id, input_key))
    }

    pub fn resolve_spec_key(
        &self,
        t: &impl crate::types::Types<Ty = crate::types::Ty>,
        key: &SpecKey,
    ) -> Option<SpecId> {
        // Fast path: exact match via per-family lookup.
        if let Some(id) = self.exact_match_spec_key(key) {
            return Some(id);
        }
        let query_tys = fully_typed_key(&key.input)?;
        let family = self.families.get(&SpecFamilyId::from(key))?;
        best_covering_candidate(
            t,
            &query_tys,
            family.ordered.iter().copied().map(|sid| {
                let entry = self.entry(sid);
                debug_assert!(entry.is_registered);
                BestCoverCandidate {
                    id: sid,
                    key: entry.key.input.as_slice(),
                    key_var_count: entry.key_var_count,
                    precedence: entry.precedence,
                }
            }),
        )
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Iterate all `(SpecId, SpecKey)` entries in SpecId order. Used by
    /// the codegen pipeline to walk every compiled body.
    pub fn iter(&self) -> impl Iterator<Item = (SpecId, &SpecKey)> {
        self.entries
            .iter()
            .enumerate()
            .map(|(i, entry)| (SpecId(i as u32), &entry.key))
    }

    /// Resolve the executable body spec a surviving `MakeClosure` should target.
    ///
    /// `MakeClosure` stores a semantic `FnId`, not an executable `SpecId`.
    /// Resolve by finding the body-backed spec in that semantic family.
    pub(crate) fn resolve_closure_body_spec(
        &self,
        fn_id: FnId,
        mut has_body: impl FnMut(SpecId) -> bool,
    ) -> Option<SpecId> {
        self.iter()
            .find(|(sid, key)| key.fn_id == fn_id && has_body(*sid))
            .map(|(sid, _)| sid)
    }
}

fn fully_typed_key(input_key: &[KeySlot]) -> Option<Vec<Ty>> {
    let mut query_tys: Vec<Ty> = Vec::with_capacity(input_key.len());
    for slot in input_key {
        match slot {
            Some(ty) => query_tys.push(ty.clone()),
            None => return None,
        }
    }
    Some(query_tys)
}

#[cfg(test)]
impl SpecRegistry {
    /// Look up a fn's any-key SpecId. Test-only helper.
    pub fn any_key(&self, fn_id: FnId, n_params: usize) -> SpecId {
        use crate::types::Types;

        let mut t = crate::types::ConcreteTypes;
        let key: Vec<KeySlot> = (0..n_params).map(|_| Some(t.any())).collect();
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
    fn return_demand_participates_in_spec_identity() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let key = vec![Some(t.int())];
        let value = SpecKey::value(fid(7), key.clone());
        let fields = SpecKey {
            fn_id: fid(7),
            input: key,
            demand: ReturnDemand::tuple_fields(2),
        };

        let value_sid = reg.register_spec_key_with_precedence(&t, value.clone(), 0);
        let fields_sid = reg.register_spec_key_with_precedence(&t, fields.clone(), 0);

        assert_ne!(
            value_sid, fields_sid,
            "return demand is part of SpecKey identity"
        );
        assert_eq!(reg.resolve_spec_key(&t, &value), Some(value_sid));
        assert_eq!(reg.resolve_spec_key(&t, &fields), Some(fields_sid));
    }

    #[test]
    fn concrete_query_matches_var_key_with_binding() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let alpha = t.type_var(TypeVarId(0));
        let sid = reg.register(&t, fid(7), vec![alpha]);
        let query = [t.int()];
        let got = reg.resolve(&t, fid(7), &query);
        assert_eq!(got, Some(sid), "concrete query int must cover var key α");
    }

    #[test]
    fn var_query_matches_same_var_key() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let alpha = t.type_var(TypeVarId(0));
        let sid = reg.register(&t, fid(7), vec![alpha]);
        let query_alpha = t.type_var(TypeVarId(0));
        let query = [query_alpha];
        let got = reg.resolve(&t, fid(7), &query);
        assert_eq!(got, Some(sid), "Var α covers Var α");
    }

    #[test]
    fn var_query_matches_different_var_key_via_binding() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let alpha = t.type_var(TypeVarId(0));
        let sid = reg.register(&t, fid(7), vec![alpha]);
        let beta = t.type_var(TypeVarId(5));
        let query = [beta];
        let got = reg.resolve(&t, fid(7), &query);
        // Var β covers Var α with binding α ↦ Var β.
        assert_eq!(got, Some(sid));
    }

    #[test]
    fn var_query_does_not_match_concrete_key() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let int = t.int();
        let _ = reg.register(&t, fid(7), vec![int]);
        let alpha = t.type_var(TypeVarId(0));
        let query = [alpha];
        let got = reg.resolve(&t, fid(7), &query);
        // Var α NOT a subtype of int — no covering candidate.
        assert_eq!(got, None);
    }

    #[test]
    fn most_specific_wins_concrete_over_var() {
        // Both a concrete-keyed spec and a var-keyed spec cover an `int`
        // query. Dispatch must pick the concrete (most specific).
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let alpha = t.type_var(TypeVarId(0));
        let var_sid = reg.register(&t, fid(7), vec![alpha]);
        let int = t.int();
        let int_sid = reg.register(&t, fid(7), vec![int.clone()]);
        let query = [int];
        let got = reg.resolve(&t, fid(7), &query);
        assert_eq!(got, Some(int_sid), "concrete > var; got {:?}", got);
        assert_ne!(got, Some(var_sid), "must not return the var-form");
    }

    #[test]
    fn positionally_inconsistent_binding_fails() {
        // Key: (α, α). Query: (int, str). Single α can't bind both → no cover.
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let alpha = t.type_var(TypeVarId(0));
        let _ = reg.register(&t, fid(7), vec![alpha.clone(), alpha]);
        let int = t.int();
        let str_t = t.str_t();
        let query = [int, str_t];
        let got = reg.resolve(&t, fid(7), &query);
        assert_eq!(got, None, "α cannot bind to both int and str");
    }

    #[test]
    fn positionally_consistent_binding_succeeds() {
        // Key: (α, α). Query: (int, int). Single α binds to int consistently.
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let alpha = t.type_var(TypeVarId(0));
        let sid = reg.register(&t, fid(7), vec![alpha.clone(), alpha]);
        let int = t.int();
        let query = [int.clone(), int];
        let got = reg.resolve(&t, fid(7), &query);
        assert_eq!(got, Some(sid));
    }

    #[test]
    fn any_query_still_does_not_match_concrete_key() {
        // Pre-fz-try.8 invariant preserved: a saturated `any` query never
        // covers a concrete key (would be unsafe — body assumes narrow inputs).
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let int = t.int();
        let _ = reg.register(&t, fid(7), vec![int]);
        let any = t.any();
        let query = [any];
        let got = reg.resolve(&t, fid(7), &query);
        assert_eq!(got, None);
    }

    #[test]
    fn hole_slot_preserves_arity_and_skips_coverage_coordinate() {
        let mut t = crate::types::ConcreteTypes;
        let mut reg = SpecRegistry::new();
        let int = t.int();
        let str_t = t.str_t();
        let sid = reg.register_with_precedence(
            &t,
            fid(7),
            vec![Some(int.clone()), None, Some(str_t.clone())],
            0,
        );

        let atom_x = t.atom_lit("x");
        assert_eq!(
            reg.resolve(&t, fid(7), &[int.clone(), atom_x.clone(), str_t]),
            Some(sid)
        );
        assert_eq!(reg.resolve(&t, fid(7), &[int.clone(), atom_x]), None);
        let int2 = t.int();
        let atom_x2 = t.atom_lit("x");
        assert_eq!(reg.resolve(&t, fid(7), &[int, atom_x2, int2]), None);
    }
}
