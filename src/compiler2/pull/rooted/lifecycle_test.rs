use super::*;
use crate::telemetry::ConfiguredTelemetry;

fn member(n: u32) -> ProductKey {
    ProductKey::RootBackendProduct(RootId::for_test(n))
}

fn packaging() -> ProductKey {
    member(99)
}

fn membership(children: &[u32]) -> ProductDependencies {
    ProductDependencies {
        membership: children.iter().map(|n| member(*n)).collect(),
        ..ProductDependencies::default()
    }
}

fn commit(memo: &mut ProductMemo, key: ProductKey, dependencies: ProductDependencies) -> bool {
    memo.finish_completion(
        &ConfiguredTelemetry::new(),
        false,
        &key,
        ProductCompletion::Batch(vec![(key.clone(), ProductValue::Unit, dependencies)]),
        &crate::compiler2::Types::new(),
    )
}

fn retained(memo: &ProductMemo) -> HashSet<ProductKey> {
    memo.rooted[&packaging()].parents.keys().cloned().collect()
}

fn assert_original_membership(memo: &ProductMemo) {
    assert_eq!(memo.membership(&member(0)), Some(&HashSet::from([member(1)])));
    assert_eq!(retained(memo), HashSet::from([member(0), member(1)]));
    assert_eq!(memo.membership_readers[&member(1)], HashSet::from([member(0)]));
    assert!(!memo.membership_readers.contains_key(&member(2)));
}

#[test]
fn only_a_successful_replacement_can_change_committed_root_membership() {
    let tel = ConfiguredTelemetry::new();
    let types = crate::compiler2::Types::new();
    let mut memo = ProductMemo::default();
    assert!(commit(&mut memo, member(1), membership(&[])));
    assert!(commit(&mut memo, member(2), membership(&[])));
    assert!(commit(&mut memo, member(0), membership(&[1])));
    memo.register_rooted(packaging(), member(0), &types);
    memo.rooted.get_mut(&packaging()).unwrap().changes.clear();
    memo.invalidate_products(&tel, [member(0)], &types);
    assert_original_membership(&memo);

    assert!(memo.begin(member(0)));
    memo.unblock(&member(0), membership(&[2]));
    assert_original_membership(&memo);
    assert!(
        memo.pending_dependencies[&member(0)].membership.is_empty(),
        "waiting records reads, but cannot publish prospective membership"
    );

    assert!(memo.begin(member(0)));
    memo.abort(&member(0));
    assert_original_membership(&memo);
    assert!(!memo.pending_dependencies.contains_key(&member(0)));

    assert!(memo.begin(member(0)));
    memo.invalidate_products(&tel, [member(0)], &types);
    assert!(
        !commit(&mut memo, member(0), membership(&[2])),
        "an invalidated in-flight completion must reject its prospective edge"
    );
    assert_original_membership(&memo);

    let mut left = membership(&[2]);
    left.products.insert(member(7), Some(1));
    let mut right = membership(&[]);
    right.products.insert(member(7), Some(2));
    assert!(
        !memo.finish_completion(
            &tel,
            false,
            &member(0),
            ProductCompletion::RecursiveGroup(vec![
                (member(0), ProductValue::Unit, left),
                (member(2), ProductValue::Unit, right),
            ]),
            &types,
        ),
        "a recursive completion with mixed external generations must reject its prospective membership"
    );
    assert_original_membership(&memo);

    assert!(commit(&mut memo, member(0), membership(&[2])));
    assert_eq!(retained(&memo), HashSet::from([member(0), member(2)]));
    assert!(!memo.membership_readers.contains_key(&member(1)));
    assert_eq!(memo.membership_readers[&member(2)], HashSet::from([member(0)]));
}

struct EqualMemberProducers {
    types: crate::compiler2::Types,
}

impl ProductProducers for EqualMemberProducers {
    fn product_types(&self) -> &crate::compiler2::Types {
        &self.types
    }

    fn produce(&mut self, context: &mut ProductReadContext<'_>, key: &ProductKey) -> PullOutcome {
        if key == &member(0) {
            context.include_product(member(1));
        } else if key == &packaging() {
            if let Err(waits) = context.read_rooted_products(packaging(), member(0), &self.types) {
                return PullOutcome::Waiting(waits);
            }
        } else if matches!(key, ProductKey::NativeProgram(_)) {
            if context
                .read_product(&ConfiguredTelemetry::new(), packaging(), &self.types)
                .is_none()
            {
                return PullOutcome::wait_on_product(packaging());
            }
        } else {
            assert_eq!(key, &member(1));
        }
        PullOutcome::Produced(ProductValue::Unit)
    }
}

#[test]
fn equal_member_reproduction_restores_native_readiness_without_packaging() {
    let tel = ConfiguredTelemetry::new();
    let evaluations = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&evaluations);
    tel.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
        PRODUCT_EVALUATED_EVENT,
        move |_, _, _, key, _, _| observed.borrow_mut().push(key.clone()),
    );
    let mut driver = ProductDriver::new(&tel, RootId::for_test(99));
    let mut producers = EqualMemberProducers {
        types: crate::compiler2::Types::new(),
    };
    let native = ProductKey::NativeProgram(RootId::for_test(99));
    for key in [member(1), member(0), packaging(), native.clone()] {
        assert!(matches!(driver.pull(&mut producers, key), PullOutcome::Produced(_)));
    }
    let root_generation = driver.session().memo.generation(&packaging());
    let native_generation = driver.session().memo.generation(&native);
    assert_eq!(
        evaluations.borrow().as_slice(),
        &[member(1), member(0), packaging(), native.clone()]
    );
    evaluations.borrow_mut().clear();
    driver
        .session_mut()
        .memo
        .observed_products
        .extend([packaging(), native.clone()]);
    driver.session_mut().memo.external_changes.clear();

    driver
        .session_mut()
        .memo
        .invalidate_products(&tel, [member(0)], &producers.types);
    assert!(
        !driver.session().memo.external_state(&native).settled,
        "a dirty rooted member must make its native reader unready"
    );
    assert_eq!(
        driver.session().memo.external_changes.len(),
        2,
        "root and native publish the readiness transition exactly once"
    );
    assert_eq!(
        driver.pull(&mut producers, native.clone()),
        PullOutcome::wait_on_product(member(0))
    );
    assert!(matches!(
        driver.pull(&mut producers, member(0)),
        PullOutcome::Produced(_)
    ));
    assert!(
        driver.session().memo.external_state(&native).settled,
        "equal reproduction must restore readiness through the retained root reader"
    );
    assert_eq!(
        driver.session().memo.external_changes.len(),
        4,
        "equal reproduction publishes both readiness restorations"
    );
    for key in [packaging(), native.clone()] {
        let session = driver.session();
        let changes = session
            .memo
            .external_changes
            .iter()
            .filter(|change| change.key == key)
            .collect::<Vec<_>>();
        assert_eq!(
            changes
                .iter()
                .map(|change| (change.old_settled, change.new_settled))
                .collect::<Vec<_>>(),
            [(true, false), (false, true)]
        );
        assert!(changes.iter().all(|change| change.old_revision == change.new_revision));
    }
    assert!(matches!(
        driver.pull(&mut producers, native.clone()),
        PullOutcome::Produced(_)
    ));
    assert_eq!(
        evaluations.borrow().as_slice(),
        &[member(0)],
        "validating an equal member must not execute packaging or native producers again"
    );
    assert_eq!(driver.session().memo.generation(&packaging()), root_generation);
    assert_eq!(driver.session().memo.generation(&native), native_generation);
    assert!(driver.session().memo.rooted[&packaging()].dirty.is_empty());
    assert!(driver.session().memo.rooted[&packaging()].changes.is_empty());
}

#[test]
fn replacing_a_root_seed_removes_empty_reverse_subscriptions() {
    let mut memo = ProductMemo::default();
    let types = crate::compiler2::Types::new();
    for (node, children) in [(0, vec![1]), (1, vec![2]), (2, vec![]), (3, vec![2])] {
        assert!(commit(&mut memo, member(node), membership(&children)));
    }
    memo.register_rooted(packaging(), member(0), &types);
    assert_eq!(retained(&memo), HashSet::from([member(0), member(1), member(2)]));
    memo.register_rooted(packaging(), member(3), &types);
    assert_eq!(retained(&memo), HashSet::from([member(2), member(3)]));
    assert!(!memo.rooted_readers.contains_key(&member(0)));
    assert!(!memo.rooted_readers.contains_key(&member(1)));
    assert_eq!(memo.rooted_readers[&member(2)], HashSet::from([packaging()]));
    assert_eq!(memo.rooted_readers[&member(3)], HashSet::from([packaging()]));
    assert!(memo.rooted_readers.values().all(|readers| !readers.is_empty()));

    memo.rooted.get_mut(&packaging()).unwrap().changes.clear();
    memo.rooted.get_mut(&packaging()).unwrap().dirty.clear();
    assert!(commit(&mut memo, member(0), membership(&[4])));
    assert_eq!(retained(&memo), HashSet::from([member(2), member(3)]));
    assert!(
        memo.rooted[&packaging()].changes.is_empty(),
        "a withdrawn seed must no longer mutate the root subscription"
    );
    assert!(memo.rooted[&packaging()].dirty.is_empty());
}

#[test]
fn clean_ordinary_and_rooted_reads_allocate_no_visiting_set() {
    let types = crate::compiler2::Types::new();
    let mut memo = ProductMemo::default();
    assert!(commit(&mut memo, member(0), membership(&[])));
    assert!(commit(&mut memo, packaging(), membership(&[])));
    memo.register_rooted(packaging(), member(0), &types);
    let root = memo.rooted.get_mut(&packaging()).unwrap();
    root.dirty.clear();
    root.changes.clear();
    for key in [member(0), packaging()] {
        let mut visiting = HashSet::new();
        assert_eq!(memo.stale_dependency_inner(&key, &mut visiting, &types), None);
        assert_eq!(
            visiting.capacity(),
            0,
            "a clean product must return before allocating a cycle guard"
        );
    }
}

#[test]
fn a_mixed_membership_and_value_backedge_shares_the_stale_visit_guard() {
    let tel = ConfiguredTelemetry::new();
    let types = crate::compiler2::Types::new();
    let mut memo = ProductMemo::default();
    assert!(commit(&mut memo, packaging(), membership(&[])));
    let mut dependency = membership(&[]);
    dependency.products.insert(packaging(), memo.generation(&packaging()));
    assert!(commit(&mut memo, member(0), dependency));
    memo.register_rooted(packaging(), member(0), &types);
    let root = memo.rooted.get_mut(&packaging()).unwrap();
    root.dirty.clear();
    root.changes.clear();
    memo.mutate_product_wave(&tel, vec![(ReaderMutation::Dirty, member(0))], &types);
    let mut visiting = HashSet::new();
    let stale = memo.stale_dependency_inner(&packaging(), &mut visiting, &types);
    assert!(
        matches!(stale, Some(key) if key == packaging() || key == member(0)),
        "a dirty cycle must produce an exact validation request rather than returning a cache hit"
    );
    assert!(
        visiting.is_empty(),
        "every stale traversal frame must unwind its own guard"
    );
}
