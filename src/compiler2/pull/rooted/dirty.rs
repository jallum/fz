//! Sparse demand over the existing membership witness, not another membership graph.

use super::*;

#[derive(Debug, Default)]
struct DirtyNode {
    marked: bool,
    waiting: Option<ProductRequestId>,
    children: IndexMap<ProductKey, ()>,
    active_position: Cell<Option<usize>>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(id: u32) -> ProductKey {
        ProductKey::RootBackendProduct(RootId::for_test(id))
    }

    fn visited(
        index: &DirtyWitness,
        seed: &ProductKey,
        parents: &HashMap<ProductKey, Option<ProductKey>>,
    ) -> HashSet<ProductKey> {
        let mut cursor = index.first(seed).0;
        let mut visited = HashSet::new();
        while let Some(key) = cursor {
            visited.insert(key.clone());
            cursor = index.next(&key, true, parents);
        }
        visited
    }

    #[test]
    fn a_new_dirty_sibling_remains_after_the_active_owner() {
        let [seed, first, added] = [0, 1, 2].map(key);
        let parents = HashMap::from([
            (seed.clone(), None),
            (first.clone(), Some(seed.clone())),
            (added.clone(), Some(seed.clone())),
        ]);
        let mut index = DirtyWitness::default();
        index.insert(first.clone(), &parents);
        assert_eq!(index.first(&seed).0, Some(first));
        index.insert(added.clone(), &parents);
        assert!(
            visited(&index, &seed, &parents).contains(&added),
            "new off-path work cannot be left behind the cursor"
        );
    }

    #[test]
    fn off_active_reparent_keeps_its_dirty_branch_reachable_without_rewinding() {
        let [seed, parent, first, other, alternative, moved] = [0, 1, 2, 3, 4, 5].map(key);
        let mut parents = HashMap::from([
            (seed.clone(), None),
            (parent.clone(), Some(seed.clone())),
            (first.clone(), Some(seed.clone())),
            (alternative.clone(), Some(seed.clone())),
            (other.clone(), Some(parent.clone())),
            (moved.clone(), Some(parent.clone())),
        ]);
        let mut index = DirtyWitness::default();
        for member in [&moved, &other, &first] {
            index.insert(member.clone(), &parents);
        }
        let active = index.first(&seed).0.unwrap();
        let (moving, previous) = if active == first {
            (moved, parent)
        } else {
            (first, seed.clone())
        };
        index.take_maintenance();
        parents.insert(moving.clone(), Some(alternative.clone()));
        index.reparent(&moving, &previous, &alternative, &parents);
        assert_eq!(index.take_maintenance().1, 0, "an untouched active path needs no reset");
        assert!(visited(&index, &seed, &parents).contains(&moving));
    }

    #[test]
    fn active_branch_reparent_keeps_its_unchanged_ancestor_prefix() {
        for size in [8_u32, 32, 64] {
            let mut parents = (0..size)
                .map(|id| (key(id), id.checked_sub(1).map(key)))
                .collect::<HashMap<_, _>>();
            let [left, right, leaf] = [size, size + 1, size + 2].map(key);
            parents.insert(left.clone(), Some(key(size - 1)));
            parents.insert(right.clone(), Some(key(size - 1)));
            parents.insert(leaf.clone(), Some(left.clone()));
            let mut index = DirtyWitness::default();
            index.insert(leaf.clone(), &parents);
            let mut visits = index.first(&key(0)).1;
            let mut prior = left.clone();
            for turn in 0..size {
                let next = if turn % 2 == 0 { &right } else { &left };
                parents.insert(leaf.clone(), Some(next.clone()));
                index.reparent(&leaf, &prior, next, &parents);
                let (first, cost) = index.first(&key(0));
                assert_eq!(first, Some(leaf.clone()));
                visits += cost;
                prior = next.clone();
            }
            assert!(
                visits <= u64::from(size) * 4 + 4,
                "common ancestors cannot be revisited on every local support change: {visits}"
            );
            assert!(
                index.take_maintenance().1 <= u64::from(size) * 2,
                "only the moved two-node suffix is rewound"
            );
        }
    }

    #[test]
    fn active_reparent_keeps_old_siblings_and_the_dirty_alternative_gate() {
        let [seed, old, alternative, moving, sibling] = [0, 1, 2, 3, 4].map(key);
        let mut parents = HashMap::from([
            (seed.clone(), None),
            (old.clone(), Some(seed.clone())),
            (alternative.clone(), Some(seed.clone())),
            (moving.clone(), Some(old.clone())),
            (sibling.clone(), Some(old.clone())),
        ]);
        let mut index = DirtyWitness::default();
        for member in [&moving, &sibling, &alternative] {
            index.insert(member.clone(), &parents);
        }
        assert_eq!(index.first(&seed).0, Some(moving.clone()));
        parents.insert(moving.clone(), Some(alternative.clone()));
        index.reparent(&moving, &old, &alternative, &parents);
        assert_eq!(index.first(&seed).0, Some(sibling.clone()));
        index.remove(&sibling, &parents);
        assert_eq!(
            index.first(&seed).0,
            Some(alternative.clone()),
            "dirty new owner gates its moved subtree"
        );
        index.remove(&alternative, &parents);
        assert_eq!(index.first(&seed).0, Some(moving));
    }

    #[test]
    fn a_wide_dirty_frontier_advances_without_rescanning_siblings() {
        for size in [8_u32, 64, 256] {
            let seed = key(0);
            let mut parents = HashMap::from([(seed.clone(), None)]);
            let mut index = DirtyWitness::default();
            for id in 1..=size {
                let member = key(id);
                parents.insert(member.clone(), Some(seed.clone()));
                index.insert(member, &parents);
            }
            let mut visits = 0;
            let mut count = 0;
            loop {
                let (member, work) = index.first(&seed);
                visits += work;
                let Some(member) = member else {
                    break;
                };
                index.remove(&member, &parents);
                count += 1;
            }
            assert_eq!(count, size);
            assert_eq!(visits, u64::from(size) + 1);
            let (updates, rewinds) = index.take_maintenance();
            assert!(
                updates + rewinds <= u64::from(size) * 10 + 4,
                "marking and removal stay linear across the entire frontier"
            );
        }
    }
}

#[derive(Debug, Default)]
pub(in crate::compiler2::pull) struct DirtyWitness {
    nodes: HashMap<ProductKey, DirtyNode>,
    marked: usize,
    active: RefCell<Vec<ProductKey>>,
    updates: Cell<u64>,
    rewinds: Cell<u64>,
}

impl DirtyWitness {
    pub(in crate::compiler2::pull) fn admit(&mut self, key: &ProductKey, request: ProductRequestId) -> bool {
        let Some(node) = self.nodes.get_mut(key).filter(|node| node.marked) else {
            return false;
        };
        if node.waiting == Some(request) {
            return false;
        }
        assert!(
            node.waiting.is_none(),
            "retired frame admission must be released before replacement"
        );
        node.waiting = Some(request);
        self.updates.set(self.updates.get() + 1);
        true
    }

    pub(in crate::compiler2::pull) fn release(&mut self, key: &ProductKey, request: ProductRequestId) {
        if let Some(node) = self.nodes.get_mut(key)
            && node.waiting == Some(request)
        {
            node.waiting = None;
            self.updates.set(self.updates.get() + 1);
        }
    }

    pub(super) fn waiting(&self, key: &ProductKey) -> Option<ProductRequestId> {
        self.nodes.get(key).and_then(|node| node.waiting)
    }

    pub(super) fn children(&self, key: &ProductKey) -> impl Iterator<Item = &ProductKey> {
        self.nodes.get(key).into_iter().flat_map(|node| node.children.keys())
    }

    pub(super) fn on_clear_active_prefix(&self, key: &ProductKey) -> bool {
        self.nodes.get(key).is_some_and(|node| {
            !node.marked
                && node
                    .active_position
                    .get()
                    .is_some_and(|position| self.active.borrow().get(position) == Some(key))
        })
    }

    pub(in crate::compiler2::pull) fn is_empty(&self) -> bool {
        self.marked == 0
    }

    pub(super) fn contains(&self, key: &ProductKey) -> bool {
        self.nodes.get(key).is_some_and(|node| node.marked)
    }

    pub(in crate::compiler2::pull) fn clear(&mut self) {
        self.updates.set(self.updates.get() + self.nodes.len() as u64);
        self.rewinds
            .set(self.rewinds.get() + self.active.get_mut().len() as u64);
        self.nodes.clear();
        self.marked = 0;
        self.active.get_mut().clear();
    }

    fn insert_child(&mut self, parent: &ProductKey, child: ProductKey) {
        self.nodes.entry(parent.clone()).or_default().children.insert(child, ());
    }

    fn remove_child(&mut self, parent: &ProductKey, child: &ProductKey) {
        self.nodes
            .get_mut(parent)
            .expect("indexed ancestor")
            .children
            .swap_remove(child);
    }

    fn truncate_active(&mut self, length: usize) {
        let active = self.active.get_mut();
        if length >= active.len() {
            return;
        }
        self.rewinds.set(self.rewinds.get() + (active.len() - length) as u64);
        active.truncate(length);
    }

    fn ensure_path(&mut self, key: &ProductKey, parents: &HashMap<ProductKey, Option<ProductKey>>) {
        if self.nodes.contains_key(key) {
            return;
        }
        let mut cursor = key.clone();
        self.nodes.insert(cursor.clone(), DirtyNode::default());
        self.updates.set(self.updates.get() + 1);
        while let Some(parent) = parents.get(&cursor).expect("indexed demand has a witness") {
            let indexed = self.nodes.contains_key(parent);
            self.insert_child(parent, cursor);
            self.updates.set(self.updates.get() + 1);
            if indexed {
                return;
            }
            self.updates.set(self.updates.get() + 1);
            cursor = parent.clone();
        }
    }

    pub(super) fn insert(&mut self, key: ProductKey, parents: &HashMap<ProductKey, Option<ProductKey>>) -> bool {
        self.ensure_path(&key, parents);
        let node = self.nodes.get_mut(&key).expect("indexed member");
        if std::mem::replace(&mut node.marked, true) {
            return false;
        }
        self.marked += 1;
        self.updates.set(self.updates.get() + 1);
        let active = self.active.get_mut();
        if let Some(position) = node
            .active_position
            .get()
            .filter(|position| active.get(*position) == Some(&key))
        {
            self.truncate_active(position + 1);
        }
        true
    }

    pub(super) fn remove(&mut self, key: &ProductKey, parents: &HashMap<ProductKey, Option<ProductKey>>) -> bool {
        let Some(node) = self.nodes.get_mut(key) else {
            return false;
        };
        if !std::mem::replace(&mut node.marked, false) {
            return false;
        }
        node.waiting = None;
        self.marked -= 1;
        self.updates.set(self.updates.get() + 1);
        self.prune(key, parents);
        true
    }

    fn prune(&mut self, key: &ProductKey, parents: &HashMap<ProductKey, Option<ProductKey>>) {
        let mut cursor = Some(key.clone());
        while let Some(key) = cursor {
            let Some(node) = self.nodes.get(&key) else {
                break;
            };
            self.updates.set(self.updates.get() + 1);
            if node.marked {
                break;
            }
            if let Some((child, ())) = node.children.first() {
                let active = self.active.get_mut();
                if active.last() == Some(&key) {
                    self.nodes[child].active_position.set(Some(active.len()));
                    active.push(child.clone());
                }
                break;
            }
            let active = self.active.get_mut();
            if let Some(position) = node
                .active_position
                .get()
                .filter(|position| active.get(*position) == Some(&key))
            {
                self.truncate_active(position);
            }
            self.nodes.remove(&key);
            self.updates.set(self.updates.get() + 1);
            cursor = parents[&key].clone();
            if let Some(parent) = &cursor {
                self.remove_child(parent, &key);
                self.updates.set(self.updates.get() + 1);
            }
        }
    }

    pub(super) fn reparent(
        &mut self,
        key: &ProductKey,
        previous: &ProductKey,
        parent: &ProductKey,
        parents: &HashMap<ProductKey, Option<ProductKey>>,
    ) {
        if !self.nodes.contains_key(key) {
            return;
        }
        let active = self.active.get_mut();
        if let Some(position) = self.nodes[key]
            .active_position
            .get()
            .filter(|position| active.get(*position) == Some(key))
        {
            self.truncate_active(position);
        }
        self.remove_child(previous, key);
        self.ensure_path(parent, parents);
        self.insert_child(parent, key.clone());
        self.updates.set(self.updates.get() + 2);
        self.prune(previous, parents);
    }

    pub(super) fn first(&self, seed: &ProductKey) -> (Option<ProductKey>, u64) {
        if self.is_empty() {
            return (None, 0);
        }
        let mut active = self.active.borrow_mut();
        if active.is_empty() {
            active.push(seed.clone());
            self.nodes[seed].active_position.set(Some(0));
        }
        let mut visits = 0;
        loop {
            let key = active.last().expect("nonempty sparse demand");
            let node = &self.nodes[key];
            visits += 1;
            if node.marked {
                return (Some(key.clone()), visits);
            }
            let child = node
                .children
                .first()
                .expect("clean indexed ancestor has dirty descendants")
                .0
                .clone();
            self.nodes[&child].active_position.set(Some(active.len()));
            active.push(child);
        }
    }

    pub(super) fn next(
        &self,
        key: &ProductKey,
        descend: bool,
        parents: &HashMap<ProductKey, Option<ProductKey>>,
    ) -> Option<ProductKey> {
        if descend && let Some((child, ())) = self.nodes[key].children.first() {
            return Some(child.clone());
        }
        let mut cursor = key;
        while let Some(parent) = parents[cursor].as_ref() {
            self.rewinds.set(self.rewinds.get() + 1);
            let siblings = &self.nodes[parent].children;
            let index = siblings.get_index_of(cursor).expect("indexed witness child");
            if let Some((sibling, ())) = siblings.get_index(index + 1) {
                return Some(sibling.clone());
            }
            cursor = parent;
        }
        None
    }

    pub(super) fn take_maintenance(&self) -> (u64, u64) {
        (self.updates.replace(0), self.rewinds.replace(0))
    }
}
