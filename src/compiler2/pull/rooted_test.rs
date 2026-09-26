use super::*;
use crate::telemetry::ConfiguredTelemetry;

fn key(n: u32) -> ProductKey {
    ProductKey::RootBackendProduct(RootId::for_test(n))
}

fn graph(memo: &mut ProductMemo, node: u32, children: &[u32]) {
    graph_with_telemetry(memo, node, children, &ConfiguredTelemetry::new());
}

fn graph_with_telemetry(memo: &mut ProductMemo, node: u32, children: &[u32], tel: &ConfiguredTelemetry) {
    let types = crate::compiler2::Types::new();
    let current = key(node);
    memo.finish_completion(
        tel,
        false,
        &current,
        ProductCompletion::Single(
            ProductValue::Unit,
            ProductDependencies {
                membership: children.iter().map(|n| key(*n)).collect(),
                ..ProductDependencies::default()
            },
        ),
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
fn alternate_repair_uses_current_children_after_reparent_and_reattachment() {
    let mut memo = ProductMemo::default();
    graph(&mut memo, 0, &[1]);
    graph(&mut memo, 1, &[2]);
    graph(&mut memo, 2, &[2]);
    memo.register_rooted(key(99), key(0), &super::super::super::types::Types::new());
    graph(&mut memo, 0, &[1, 4]);
    graph(&mut memo, 4, &[2]);
    graph(&mut memo, 1, &[]);
    assert_eq!(memo.rooted[&key(99)].parents[&key(2)], Some(key(4)));
    assert_eq!(memo.rooted[&key(99)].last_detached, 0);

    graph(&mut memo, 2, &[2, 3]);
    graph(&mut memo, 3, &[2]);
    for _ in 0..2 {
        assert_eq!(memo.rooted[&key(99)].parents[&key(3)], Some(key(2)));
        memo.rooted.get_mut(&key(99)).unwrap().changes.clear();
        graph(&mut memo, 4, &[]);
        assert_eq!(members(&memo), HashSet::from([key(0), key(1), key(4)]));
        assert_eq!(memo.rooted[&key(99)].changes, HashSet::from([key(2), key(3)]));
        assert_eq!(memo.rooted[&key(99)].last_detached, 2);
        assert!(!memo.rooted_readers.contains_key(&key(2)));
        assert!(!memo.rooted_readers.contains_key(&key(3)));
        graph(&mut memo, 4, &[2]);
        assert_eq!(members(&memo), (0..5).map(key).collect());
    }
}

#[test]
fn absent_self_and_unreached_alternates_need_no_cycle_proof() {
    for candidates in [vec![], vec![1], vec![1, 2]] {
        let mut memo = ProductMemo::default();
        graph(&mut memo, 0, &[1]);
        graph(&mut memo, 1, &[]);
        for candidate in &candidates {
            graph(&mut memo, *candidate, &[1]);
        }
        memo.register_rooted(key(99), key(0), &super::super::super::types::Types::new());
        let tel = ConfiguredTelemetry::new();
        let proof = Rc::new(RefCell::new(ProductValidation::default()));
        let observed = Rc::clone(&proof);
        tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
            &["fz", "compiler2", "pull", "product", "validation"],
            move |_, _, _, _, work| observed.borrow_mut().include(*work),
        );
        graph_with_telemetry(&mut memo, 0, &[], &tel);
        assert_eq!(members(&memo), HashSet::from([key(0)]));
        assert_eq!(proof.borrow().reparent_candidates, (candidates.len() * 2) as u64);
        assert_eq!(proof.borrow().reparent_proof_nodes, 0);
    }
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
    rooted.dirty.clear();
    rooted.mark_dirty(&key(1));
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
        ProductCompletion::RecursiveGroup(completion),
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
                let mut ancestors = HashSet::from([member]);
                let mut cursor = Some(parent);
                while let Some(ancestor) = cursor {
                    assert!(
                        ancestors.insert(ancestor),
                        "the witness is acyclic even when the demand graph is not"
                    );
                    cursor = rooted.parents[ancestor].as_ref();
                }
            } else {
                assert_eq!(member, &rooted.seed);
            }
        }
        let mut expected_children = HashMap::<ProductKey, HashSet<ProductKey>>::new();
        for (member, parent) in &rooted.parents {
            if let Some(parent) = parent {
                expected_children
                    .entry(parent.clone())
                    .or_default()
                    .insert(member.clone());
            }
        }
        let actual_children = rooted
            .children
            .iter()
            .filter(|(_, children)| !children.is_empty())
            .map(|(parent, children)| (parent.clone(), children.clone()))
            .collect::<HashMap<_, _>>();
        assert_eq!(
            actual_children, expected_children,
            "the child index is exactly the selected-parent relation"
        );
    }
}
