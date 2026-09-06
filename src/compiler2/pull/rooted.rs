//! Rooted demand is a witness over the memo's committed membership edges.

use super::*;

#[derive(Debug)]
pub(super) struct RootedProducts {
    seed: ProductKey,
    parents: HashMap<ProductKey, Option<ProductKey>>,
    children: HashMap<ProductKey, HashSet<ProductKey>>,
    pub(super) dirty: HashSet<ProductKey>,
    pub(super) changes: HashSet<ProductKey>,
    #[cfg(test)]
    last_detached: usize,
}

impl RootedProducts {
    fn new(seed: ProductKey) -> Self {
        Self {
            seed,
            parents: HashMap::new(),
            children: HashMap::new(),
            dirty: HashSet::new(),
            changes: HashSet::new(),
            #[cfg(test)]
            last_detached: 0,
        }
    }

    fn attach(
        &mut self,
        memo: &ProductMemo,
        key: ProductKey,
        parent: Option<ProductKey>,
        types: &super::super::types::Types,
    ) -> HashSet<ProductKey> {
        let mut pending = vec![(key, parent)];
        let mut added = HashSet::new();
        while let Some((key, parent)) = pending.pop() {
            if self.parents.contains_key(&key) {
                continue;
            }
            if let Some(parent) = &parent {
                self.children.entry(parent.clone()).or_default().insert(key.clone());
            }
            self.parents.insert(key.clone(), parent);
            self.dirty.insert(key.clone());
            self.changes.insert(key.clone());
            added.insert(key.clone());
            let mut children = memo.membership(&key).into_iter().flatten().collect::<Vec<_>>();
            children.sort_by(|left, right| right.semantic_cmp(left, types));
            pending.extend(children.into_iter().map(|child| (child.clone(), Some(key.clone()))));
        }
        added
    }

    fn below(&self, key: &ProductKey, ancestor: &ProductKey) -> bool {
        let mut cursor = Some(key);
        while let Some(key) = cursor {
            if key == ancestor {
                return true;
            }
            cursor = self.parents.get(key).and_then(Option::as_ref);
        }
        false
    }

    fn reparent(&mut self, key: &ProductKey, parent: ProductKey) {
        let previous = self.parents.get_mut(key).expect("only a reached member is reparented");
        if let Some(previous) = previous.replace(parent.clone()) {
            self.children
                .get_mut(&previous)
                .expect("witness child index")
                .remove(key);
        }
        self.children.entry(parent).or_default().insert(key.clone());
    }

    fn remove_edge(
        &mut self,
        memo: &ProductMemo,
        parent: &ProductKey,
        key: &ProductKey,
        types: &super::super::types::Types,
    ) -> HashSet<ProductKey> {
        if self.parents.get(key) != Some(&Some(parent.clone())) {
            return HashSet::new();
        }
        if let Some(alternate) = memo
            .membership_readers
            .get(key)
            .into_iter()
            .flatten()
            .filter(|candidate| self.parents.contains_key(*candidate) && !self.below(candidate, key))
            .min_by(|left, right| left.semantic_cmp(right, types))
        {
            self.reparent(key, alternate.clone());
            return HashSet::new();
        }
        let mut detached = HashMap::new();
        let mut pending = vec![key.clone()];
        while let Some(member) = pending.pop() {
            if detached
                .insert(
                    member.clone(),
                    (self.changes.contains(&member), self.dirty.contains(&member)),
                )
                .is_none()
            {
                pending.extend(self.children.remove(&member).into_iter().flatten());
            }
        }
        #[cfg(test)]
        {
            self.last_detached += detached.len();
        }
        self.children
            .get_mut(parent)
            .expect("removed witness has a parent")
            .remove(key);
        for member in detached.keys() {
            self.parents.remove(member);
        }
        let mut entrances = detached
            .keys()
            .flat_map(|member| {
                memo.membership_readers
                    .get(member)
                    .into_iter()
                    .flatten()
                    .filter(|parent| self.parents.contains_key(*parent))
                    .map(|parent| (member.clone(), parent.clone()))
            })
            .collect::<Vec<_>>();
        entrances.sort_by(|(left, parent), (right, next_parent)| {
            left.semantic_cmp(right, types)
                .then_with(|| parent.semantic_cmp(next_parent, types))
        });
        let mut touched = HashSet::new();
        for (member, parent) in entrances {
            touched.extend(self.attach(memo, member, Some(parent), types));
        }
        for (member, (was_changed, was_dirty)) in detached {
            if self.parents.contains_key(&member) {
                // Restoration changes a proof, not a contribution.
                if !was_changed {
                    self.changes.remove(&member);
                }
                if !was_dirty {
                    self.dirty.remove(&member);
                }
                touched.remove(&member);
                continue;
            }
            self.dirty.remove(&member);
            self.changes.insert(member.clone());
            touched.insert(member);
        }
        touched
    }

    fn replace_edges(
        &mut self,
        memo: &ProductMemo,
        owner: &ProductKey,
        previous: &HashSet<ProductKey>,
        types: &super::super::types::Types,
    ) -> HashSet<ProductKey> {
        #[cfg(test)]
        {
            self.last_detached = 0;
        }
        let next = memo
            .membership(owner)
            .expect("a successful member has committed dependencies");
        // New entry paths exist before obsolete support is repaired.
        let mut touched = HashSet::new();
        let mut added = next.difference(previous).collect::<Vec<_>>();
        let mut removed = previous.difference(next).collect::<Vec<_>>();
        added.sort_by(|left, right| left.semantic_cmp(right, types));
        removed.sort_by(|left, right| left.semantic_cmp(right, types));
        for child in added {
            touched.extend(self.attach(memo, child.clone(), Some(owner.clone()), types));
        }
        for child in removed {
            touched.extend(self.remove_edge(memo, owner, child, types));
        }
        touched
    }
}

impl ProductMemo {
    pub(super) fn rooted_member_dirty(&mut self, member: &ProductKey) -> Vec<ProductKey> {
        let readers = self.rooted_readers.get(member).cloned().unwrap_or_default();
        readers
            .into_iter()
            .filter(|reader| {
                self.rooted
                    .get_mut(reader)
                    .expect("registered root")
                    .dirty
                    .insert(member.clone())
            })
            .collect()
    }

    pub(super) fn rooted_member_refresh(&mut self, member: &ProductKey) -> Vec<ProductKey> {
        if self.has_unsettled_inputs(member) {
            return Vec::new();
        }
        let readers = self.rooted_readers.get(member).cloned().unwrap_or_default();
        readers
            .into_iter()
            .filter(|reader| {
                let rooted = self.rooted.get_mut(reader).expect("registered root");
                rooted.dirty.remove(member) && rooted.dirty.is_empty() && rooted.changes.is_empty()
            })
            .collect()
    }

    pub(super) fn rooted_stale_dependency(
        &self,
        reader: &ProductKey,
        visiting: &mut HashSet<ProductKey>,
        types: &super::super::types::Types,
    ) -> Option<ProductKey> {
        let rooted = self.rooted.get(reader)?;
        let mut dirty = rooted.dirty.iter().collect::<Vec<_>>();
        dirty.sort_by(|left, right| left.semantic_cmp(right, types));
        for member in dirty {
            if self.get(member).is_none() {
                return Some(member.clone());
            }
            if let Some(stale) = self.stale_dependency_inner(member, visiting, types) {
                return Some(stale);
            }
        }
        None
    }

    fn membership(&self, key: &ProductKey) -> Option<&HashSet<ProductKey>> {
        self.produced
            .get(key)
            .or_else(|| self.displaced.get(key))
            .map(|entry| &entry.membership)
    }

    pub(super) fn register_rooted(&mut self, reader: ProductKey, seed: ProductKey, types: &super::super::types::Types) {
        if self.rooted.get(&reader).is_some_and(|rooted| rooted.seed == seed) {
            return;
        }
        let mut rooted = RootedProducts::new(seed.clone());
        let _ = rooted.attach(self, seed, None, types);
        if let Some(previous) = self.rooted.remove(&reader) {
            for member in previous.parents.keys() {
                let readers = self.rooted_readers.get_mut(member).expect("registered member");
                readers.remove(&reader);
                if readers.is_empty() {
                    self.rooted_readers.remove(member);
                }
                if rooted.parents.contains_key(member) {
                    if !previous.changes.contains(member) {
                        rooted.changes.remove(member);
                    }
                    if !previous.dirty.contains(member) {
                        rooted.dirty.remove(member);
                    }
                } else {
                    rooted.changes.insert(member.clone());
                }
            }
            rooted.changes.extend(
                previous
                    .changes
                    .into_iter()
                    .filter(|member| !rooted.parents.contains_key(member)),
            );
        }
        for member in rooted.parents.keys() {
            self.rooted_readers
                .entry(member.clone())
                .or_default()
                .insert(reader.clone());
        }
        self.rooted.insert(reader, rooted);
    }

    pub(super) fn replace_membership_readers(&mut self, owner: &ProductKey, previous: &HashSet<ProductKey>) {
        let next = self.membership(owner).expect("committed membership");
        let removed = previous.difference(next).cloned().collect::<Vec<_>>();
        let added = next.difference(previous).cloned().collect::<Vec<_>>();
        for child in removed {
            let readers = self
                .membership_readers
                .get_mut(&child)
                .expect("committed reverse membership");
            readers.remove(owner);
            if readers.is_empty() {
                self.membership_readers.remove(&child);
            }
        }
        for child in added {
            self.membership_readers.entry(child).or_default().insert(owner.clone());
        }
    }

    pub(super) fn committed_rooted_member(
        &mut self,
        owner: &ProductKey,
        previous: &HashSet<ProductKey>,
        changed: bool,
        types: &super::super::types::Types,
    ) -> Vec<(ReaderMutation, ProductKey)> {
        let readers = self.rooted_readers.get(owner).cloned().unwrap_or_default();
        let mut invalidated = Vec::new();
        for reader in readers {
            let mut rooted = self.rooted.remove(&reader).expect("registered root reader");
            let touched = rooted.replace_edges(self, owner, previous, types);
            rooted.dirty.remove(owner);
            if changed {
                rooted.changes.insert(owner.clone());
            }
            for member in &touched {
                if rooted.parents.contains_key(member) {
                    self.rooted_readers
                        .entry(member.clone())
                        .or_default()
                        .insert(reader.clone());
                } else if let Some(readers) = self.rooted_readers.get_mut(member) {
                    readers.remove(&reader);
                    if readers.is_empty() {
                        self.rooted_readers.remove(member);
                    }
                }
            }
            if !rooted.changes.is_empty() {
                invalidated.push((ReaderMutation::Invalidate, reader.clone()));
            } else if rooted.dirty.is_empty() {
                invalidated.push((ReaderMutation::Refresh, reader.clone()));
            }
            self.rooted.insert(reader, rooted);
        }
        invalidated
    }
}

impl ProductReadContext<'_> {
    pub(crate) fn include_product(&mut self, key: ProductKey) {
        self.dependencies.membership.insert(key);
    }

    pub(crate) fn read_rooted_products(
        &mut self,
        reader: ProductKey,
        seed: ProductKey,
        types: &super::super::types::Types,
    ) -> Result<Vec<(ProductKey, Option<ProductValue>)>, Vec<PullWait>> {
        self.session.memo.register_rooted(reader.clone(), seed, types);
        let mut rooted = self.session.memo.rooted.remove(&reader).expect("registered root");
        let mut waits = Vec::new();
        rooted.dirty.retain(|member| {
            let stale =
                self.session.memo.get(member).is_none() || self.session.memo.stale_dependency(member, types).is_some();
            if stale {
                waits.push(PullWait::Product(member.clone()));
            }
            stale
        });
        let result = if waits.is_empty() {
            let mut changes = std::mem::take(&mut rooted.changes).into_iter().collect::<Vec<_>>();
            sort_product_keys(&mut changes, types);
            Ok(changes
                .into_iter()
                .map(|key| {
                    let value = rooted
                        .parents
                        .contains_key(&key)
                        .then(|| self.session.memo.get(&key).expect("ready rooted member").clone());
                    (key, value)
                })
                .collect())
        } else {
            Err(waits)
        };
        self.session.memo.rooted.insert(reader, rooted);
        result
    }

    pub(crate) fn previous_product(&self, key: &ProductKey) -> Option<&ProductValue> {
        self.session
            .memo
            .produced
            .get(key)
            .or_else(|| self.session.memo.displaced.get(key))
            .map(|entry| &entry.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::telemetry::ConfiguredTelemetry;

    fn key(n: u32) -> ProductKey {
        ProductKey::RootBackendProduct(RootId::for_test(n))
    }

    fn graph(memo: &mut ProductMemo, node: u32, children: &[u32]) {
        let types = crate::compiler2::Types::new();
        let tel = ConfiguredTelemetry::new();
        let current = key(node);
        memo.finish_completion(
            &tel,
            false,
            &current,
            ProductCompletion::Batch(vec![(
                current.clone(),
                ProductValue::Unit,
                ProductDependencies {
                    membership: children.iter().map(|n| key(*n)).collect(),
                    ..ProductDependencies::default()
                },
            )]),
            &types,
        );
    }

    fn members(memo: &ProductMemo) -> HashSet<ProductKey> {
        memo.rooted[&key(99)].parents.keys().cloned().collect()
    }

    #[test]
    fn cutting_the_only_entry_withdraws_an_internally_supported_cycle_and_reattaches_it() {
        let mut memo = ProductMemo::default();
        graph(&mut memo, 0, &[1]);
        graph(&mut memo, 1, &[2]);
        graph(&mut memo, 2, &[1]);
        memo.register_rooted(key(99), key(0), &super::super::super::types::Types::new());
        assert_eq!(members(&memo), HashSet::from([key(0), key(1), key(2)]));
        graph(&mut memo, 0, &[]);
        assert_eq!(members(&memo), HashSet::from([key(0)]));
        graph(&mut memo, 2, &[1, 3]);
        graph(&mut memo, 3, &[]);
        graph(&mut memo, 0, &[1]);
        assert_eq!(members(&memo), HashSet::from([key(0), key(1), key(2), key(3)]));
    }

    #[test]
    fn an_alternate_entry_reparents_without_visiting_the_unchanged_subtree() {
        let mut memo = ProductMemo::default();
        graph(&mut memo, 0, &[1]);
        graph(&mut memo, 1, &[2]);
        for n in 2..30 {
            graph(&mut memo, n, &[n + 1]);
        }
        graph(&mut memo, 30, &[]);
        memo.register_rooted(key(99), key(0), &super::super::super::types::Types::new());
        graph(&mut memo, 0, &[1, 31]);
        graph(&mut memo, 31, &[2]);
        memo.rooted.get_mut(&key(99)).unwrap().changes.clear();
        graph(&mut memo, 1, &[]);
        let rooted = &memo.rooted[&key(99)];
        assert_eq!(rooted.parents[&key(2)], Some(key(31)));
        assert!(
            rooted.changes.is_empty(),
            "equal products and unchanged membership produce no deltas"
        );
        assert_eq!(
            rooted.last_detached, 0,
            "a direct valid alternative never visits descendants"
        );
        assert_eq!(rooted.parents.len(), 32);
    }

    #[test]
    fn reseeding_retains_equal_shared_members_without_contribution_or_demand_work() {
        let mut memo = ProductMemo::default();
        graph(&mut memo, 0, &[1]);
        graph(&mut memo, 1, &[]);
        graph(&mut memo, 2, &[1]);
        let types = super::super::super::types::Types::new();
        memo.register_rooted(key(99), key(0), &types);
        let rooted = memo.rooted.get_mut(&key(99)).unwrap();
        rooted.changes.clear();
        rooted.dirty.clear();
        memo.register_rooted(key(99), key(2), &types);
        assert_eq!(members(&memo), HashSet::from([key(1), key(2)]));
        assert_eq!(memo.rooted[&key(99)].changes, HashSet::from([key(0), key(2)]));
        assert!(!memo.rooted[&key(99)].dirty.contains(&key(1)));
    }

    #[test]
    fn an_external_entry_inside_a_detached_cycle_restores_only_its_reachable_component() {
        for cycle in [false, true] {
            let mut memo = ProductMemo::default();
            graph(&mut memo, 0, &[1]);
            graph(&mut memo, 1, &[2]);
            graph(&mut memo, 2, &[3]);
            graph(&mut memo, 3, if cycle { &[2] } else { &[] });
            memo.register_rooted(key(99), key(0), &super::super::super::types::Types::new());
            graph(&mut memo, 0, &[1, 4]);
            graph(&mut memo, 4, &[3]);
            let rooted = memo.rooted.get_mut(&key(99)).unwrap();
            rooted.changes.clear();
            rooted.dirty.clear();
            graph(&mut memo, 1, &[]);
            let expected = if cycle { vec![0, 1, 2, 3, 4] } else { vec![0, 1, 3, 4] };
            assert_eq!(members(&memo), expected.into_iter().map(key).collect());
            assert_eq!(
                memo.rooted[&key(99)].changes,
                if cycle { HashSet::new() } else { HashSet::from([key(2)]) }
            );
            assert!(
                memo.rooted[&key(99)].dirty.is_empty(),
                "repaired witness support never demands clean restored bodies"
            );
        }
    }

    #[test]
    fn transactional_replacement_uses_the_new_entry_before_retiring_the_old_edge() {
        let mut memo = ProductMemo::default();
        graph(&mut memo, 0, &[1]);
        graph(&mut memo, 1, &[2]);
        graph(&mut memo, 2, &[]);
        graph(&mut memo, 3, &[2]);
        memo.register_rooted(key(99), key(0), &super::super::super::types::Types::new());
        memo.rooted.get_mut(&key(99)).unwrap().changes.clear();
        graph(&mut memo, 1, &[3]);
        assert_eq!(members(&memo), HashSet::from([key(0), key(1), key(2), key(3)]));
        assert_eq!(memo.rooted[&key(99)].changes, HashSet::from([key(3)]));
    }

    #[test]
    fn an_ordinary_refresh_cannot_clear_another_rooted_members_pending_work() {
        let mut memo = ProductMemo::default();
        graph(&mut memo, 0, &[1]);
        graph(&mut memo, 1, &[]);
        graph(&mut memo, 99, &[]);
        let types = super::super::super::types::Types::new();
        memo.register_rooted(key(99), key(0), &types);
        let rooted = memo.rooted.get_mut(&key(99)).unwrap();
        rooted.changes.clear();
        rooted.dirty = HashSet::from([key(1)]);
        memo.dirty_descendants.insert(key(99));
        memo.mutate_product_wave(
            &ConfiguredTelemetry::new(),
            vec![(ReaderMutation::Refresh, key(99))],
            &types,
        );
        assert!(memo.dirty_descendants.contains(&key(99)));
        assert!(!memo.external_state(&key(99)).settled);
    }

    #[test]
    fn a_multi_owner_commit_repairs_against_all_final_edges_without_membership_churn() {
        let mut memo = ProductMemo::default();
        graph(&mut memo, 0, &[1, 2]);
        graph(&mut memo, 1, &[3]);
        graph(&mut memo, 2, &[4]);
        graph(&mut memo, 3, &[]);
        graph(&mut memo, 4, &[]);
        let types = super::super::super::types::Types::new();
        memo.register_rooted(key(99), key(0), &types);
        memo.rooted.get_mut(&key(99)).unwrap().changes.clear();
        let completion = [(1, 4), (2, 3)]
            .into_iter()
            .map(|(owner, child)| {
                (
                    key(owner),
                    ProductValue::Unit,
                    ProductDependencies {
                        membership: HashSet::from([key(child)]),
                        ..ProductDependencies::default()
                    },
                )
            })
            .collect();
        memo.finish_completion(
            &ConfiguredTelemetry::new(),
            false,
            &key(1),
            ProductCompletion::Batch(completion),
            &types,
        );
        assert_eq!(members(&memo), (0..5).map(key).collect());
        assert!(memo.rooted[&key(99)].changes.is_empty());
        assert_eq!(memo.rooted[&key(99)].parents[&key(3)], Some(key(2)));
        assert_eq!(memo.rooted[&key(99)].parents[&key(4)], Some(key(1)));
    }

    #[test]
    fn local_witness_selection_and_repair_work_ignore_membership_insertion_order() {
        let edges = [(0, vec![1, 4]), (1, vec![2]), (2, vec![3]), (3, vec![2]), (4, vec![3])];
        let types = super::super::super::types::Types::new();
        let mut reference = None;
        for permutation in 0..32 {
            let mut memo = ProductMemo::default();
            for index in 0..edges.len() {
                let (owner, children) = &edges[(index + permutation) % edges.len()];
                let mut children = children.clone();
                if permutation & 1 != 0 {
                    children.reverse();
                }
                graph(&mut memo, *owner, &children);
            }
            memo.register_rooted(key(99), key(0), &types);
            memo.rooted.get_mut(&key(99)).unwrap().changes.clear();
            let before = memo.rooted[&key(99)].parents.clone();
            graph(&mut memo, 1, &[]);
            let rooted = &memo.rooted[&key(99)];
            let observed = (
                before,
                rooted.parents.clone(),
                rooted.changes.clone(),
                rooted.last_detached,
            );
            if let Some(reference) = &reference {
                assert_eq!(&observed, reference);
            } else {
                reference = Some(observed);
            }
        }
    }

    #[test]
    fn randomized_committed_membership_matches_reachability_from_the_root() {
        let mut memo = ProductMemo::default();
        let mut edges = HashMap::<u32, Vec<u32>>::new();
        memo.register_rooted(key(99), key(0), &super::super::super::types::Types::new());
        let mut random = 0x9723_a712_u64;
        for _ in 0..1200 {
            random ^= random << 13;
            random ^= random >> 7;
            random ^= random << 17;
            let node = (random % 12) as u32;
            let before = members(&memo);
            let was_produced = memo.get(&key(node)).is_some();
            memo.rooted.get_mut(&key(99)).unwrap().changes.clear();
            let children = (0..12).filter(|n| random & (1 << (n + 12)) != 0).collect::<Vec<_>>();
            edges.insert(node, children.clone());
            graph(&mut memo, node, &children);
            let mut expected = HashSet::new();
            let mut pending = vec![0];
            while let Some(next) = pending.pop() {
                if expected.insert(key(next)) {
                    pending.extend(edges.get(&next).into_iter().flatten());
                }
            }
            assert_eq!(members(&memo), expected);
            let mut delta = before.symmetric_difference(&expected).cloned().collect::<HashSet<_>>();
            if !was_produced && expected.contains(&key(node)) {
                delta.insert(key(node));
            }
            assert_eq!(
                memo.rooted[&key(99)].changes,
                delta,
                "one committed replacement emits its exact net contribution delta"
            );
            let rooted = &memo.rooted[&key(99)];
            for (member, parent) in &rooted.parents {
                if let Some(parent) = parent {
                    assert!(memo.membership(parent).unwrap().contains(member));
                    assert!(
                        !rooted.below(parent, member),
                        "the witness is acyclic even when the demand graph is not"
                    );
                } else {
                    assert_eq!(member, &rooted.seed);
                }
            }
        }
    }
}
#[cfg(test)]
mod lifecycle_test;
