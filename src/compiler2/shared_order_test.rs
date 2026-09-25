use super::SharedOrder;
use std::collections::BTreeMap;
use std::rc::Rc;

#[test]
fn equal_updates_share_the_whole_inventory_and_obey_the_supplied_order() {
    let compare = |left: &i32, right: &i32| right.cmp(left);
    let mut actual = SharedOrder::default();
    for key in 0..63 {
        actual.insert(key, key, &compare);
    }
    let retained = actual.clone();
    assert!(!actual.insert(31, 31, &compare));
    assert_eq!(actual.remove(&100, &compare), None);
    assert!(actual.same_root(&retained));
    assert_eq!(actual.shared_nodes(&retained), 63);
    assert_eq!(
        actual.iter().copied().collect::<Vec<_>>(),
        (0..63).rev().collect::<Vec<_>>()
    );
    assert_eq!(actual.rank(&0, &compare), Some(62));
    actual.remove(&31, &compare);
    assert_eq!(actual.rank(&0, &compare), Some(61));
    assert_eq!(actual.get_index(31), Some(&30));
}

#[test]
fn changed_keys_preserve_prior_snapshots_and_unmodified_tree_branches() {
    let mut original = SharedOrder::default();
    for key in 0..255 {
        original.insert(key, Rc::new(key), &i32::cmp);
    }
    let retained = original.clone();
    let old_value = Rc::clone(original.lookup(&127, &i32::cmp).unwrap());
    original.insert(127, Rc::new(-127), &i32::cmp);
    assert_eq!(**retained.lookup(&127, &i32::cmp).unwrap(), 127);
    assert_eq!(**original.lookup(&127, &i32::cmp).unwrap(), -127);
    assert!(Rc::ptr_eq(&old_value, retained.lookup(&127, &i32::cmp).unwrap()));
    assert!(
        original.shared_nodes(&retained) >= 247,
        "one replacement copies at most one balanced path"
    );
    original.remove(&0, &i32::cmp);
    assert_eq!(retained.len(), 255);
    assert_eq!(original.len(), 254);
    assert!(
        original.shared_nodes(&retained) >= 235,
        "deletion preserves branches outside its balancing path"
    );
}

#[test]
fn rotations_compare_shared_subtrees_without_scanning_unchanged_rows() {
    let mut original = SharedOrder::default();
    for key in 0..4095 {
        original.insert(key, key, &i32::cmp);
    }
    let mut changed = original.clone();
    // Equal content with different path shapes after deletion/reinsertion.
    for key in [0, 1, 2, 3, 4, 5, 6, 7] {
        changed.remove(&key, &i32::cmp);
    }
    for key in [7, 6, 5, 4, 3, 2, 1, 0] {
        changed.insert(key, key, &i32::cmp);
    }
    let (equal, work) = original.equal_with_work(&changed);
    assert!(equal);
    assert!(work < 200, "rotated paths must skip shared subtrees: {work}");
    changed.insert(4094, -1, &i32::cmp);
    let (equal, work) = original.equal_with_work(&changed);
    assert!(!equal);
    assert!(
        work < 300,
        "a far changed row does not scan intervening inventory: {work}"
    );
}

#[test]
fn ordered_updates_match_a_map_and_project_each_rank_in_both_directions() {
    let mut actual = SharedOrder::default();
    let mut expected = BTreeMap::new();
    let mut random = 0x218a_b94c_u64;
    for step in 0..4000 {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        let key = (random % 127) as i32;
        if random & 256 == 0 {
            actual.insert(key, step, &i32::cmp);
            expected.insert(key, step);
        } else {
            assert_eq!(actual.remove(&key, &i32::cmp), expected.remove(&key));
        }
        assert_eq!(actual.len(), expected.len());
        assert_eq!(
            actual.entries().collect::<Vec<_>>(),
            expected.iter().collect::<Vec<_>>()
        );
        for (rank, (key, value)) in expected.iter().enumerate() {
            assert_eq!(actual.rank(key, &i32::cmp), Some(rank));
            assert_eq!(actual.lookup(key, &i32::cmp), Some(value));
            assert_eq!(actual.get_index(rank), Some(value));
        }
        assert!(actual.get_index(expected.len()).is_none());
        actual.assert_balanced();
    }
}
