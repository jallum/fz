use super::*;

fn id(n: u32) -> ValueId {
    ValueId::from_u32(n)
}

/// A map answers exactly what a hash map keyed by the same ids would: the
/// last insert wins, a missing id is absent, and `len` counts present keys.
#[test]
fn behaves_like_a_map_over_sparse_ids() {
    let mut map = ValueMap::new();
    assert_eq!(map.insert(id(5), "five"), None);
    assert_eq!(map.insert(id(2), "two"), None);
    assert_eq!(map.insert(id(5), "FIVE"), Some("five"));

    assert_eq!(map.len(), 2);
    assert_eq!(map.get(&id(5)), Some(&"FIVE"));
    assert_eq!(map.get(&id(3)), None);
    assert_eq!(map.get(&id(900)), None);
    assert_eq!(map.remove(&id(2)), Some("two"));
    assert_eq!(map.remove(&id(2)), None);
    assert_eq!(map.len(), 1);
}

/// Iteration is by id, not by insertion or hash seed, so two runs over the
/// same facts see the same sequence.
#[test]
fn iterates_in_id_order() {
    let map: ValueMap<char> = [(id(9), 'c'), (id(1), 'a'), (id(4), 'b')].into();
    assert_eq!(map.keys().collect::<Vec<_>>(), vec![id(1), id(4), id(9)]);
    assert_eq!(map.values().copied().collect::<String>(), "abc");
    assert_eq!(map.into_iter().map(|(_, v)| v).collect::<String>(), "abc");
}

/// Equality is about the entries, not about how far the backing vector grew:
/// a map that once held a high id and lost it equals a fresh one.
#[test]
fn equality_ignores_spare_capacity() {
    let mut grown = ValueMap::new();
    grown.insert(id(1), 'a');
    grown.insert(id(50), 'z');
    grown.remove(&id(50));
    let fresh: ValueMap<char> = [(id(1), 'a')].into();
    assert_eq!(grown, fresh);
    assert_ne!(grown, ValueMap::from([(id(1), 'b')]));
}

/// The entry API fills a missing slot once and counts it once.
#[test]
fn entry_fills_only_a_missing_slot() {
    let mut map = ValueMap::new();
    *map.entry(id(3)).or_insert(10) += 1;
    *map.entry(id(3)).or_insert(10) += 1;
    assert_eq!(map.get(&id(3)), Some(&12));
    assert_eq!(map.len(), 1);
}

/// Retaining drops the rejected entries and keeps `len` honest.
#[test]
fn retain_drops_rejected_entries() {
    let mut map: ValueMap<u32> = (0..6).map(|n| (id(n), n)).collect();
    map.retain(|_, n| *n % 2 == 0);
    assert_eq!(map.keys().collect::<Vec<_>>(), vec![id(0), id(2), id(4)]);
    assert_eq!(map.len(), 3);
}
