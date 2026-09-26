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
