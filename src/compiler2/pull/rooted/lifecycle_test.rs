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
        ProductCompletion::Single(ProductValue::Unit, dependencies),
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
    memo.unblock(ProductRequestId(NonZeroU64::MIN), &member(0), membership(&[2]));
    assert_original_membership(&memo);
    assert_eq!(
        memo.pending_dependencies[&member(0)].dependencies.membership,
        HashSet::from([member(2)]),
        "waiting retains the current attempt for group handoff without publishing it"
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
            if let Err(waits) =
                context.read_rooted_products(&ConfiguredTelemetry::new(), packaging(), member(0), &self.types)
            {
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
        let mut visiting = ProductValidationWalk::default();
        assert_eq!(
            memo.stale_dependency_inner(&ConfiguredTelemetry::new(), &key, &mut visiting, &types, true),
            None
        );
        assert_eq!(
            visiting.checked.capacity(),
            0,
            "a clean product must return before allocating a cycle guard"
        );
    }
}

#[test]
fn stale_membership_validates_its_owner_before_demanding_a_retired_child() {
    let tel = ConfiguredTelemetry::new();
    let types = crate::compiler2::Types::new();
    let mut memo = ProductMemo::default();
    assert!(commit(&mut memo, member(0), membership(&[])));
    assert!(commit(&mut memo, member(2), membership(&[0])));
    memo.register_rooted(packaging(), member(2), &types);
    memo.rooted.get_mut(&packaging()).unwrap().dirty.clear();
    memo.invalidate_products(&tel, [member(0), member(2)], &types);
    assert_eq!(
        memo.rooted_stale_dependency(
            &ConfiguredTelemetry::new(),
            &packaging(),
            &mut ProductValidationWalk::default(),
            &types,
            true
        ),
        Some(member(2)),
        "a child's membership is justified only after its dirty owner validates"
    );
    assert!(commit(&mut memo, member(2), membership(&[])));
    assert_eq!(
        memo.rooted_stale_dependency(
            &ConfiguredTelemetry::new(),
            &packaging(),
            &mut ProductValidationWalk::default(),
            &types,
            true
        ),
        None
    );
    assert!(!retained(&memo).contains(&member(0)));
}

#[test]
fn rooted_validation_visits_shared_ancestor_paths_once() {
    for size in [8_u32, 32, 64] {
        let tel = ConfiguredTelemetry::new();
        let measurements = Rc::new(RefCell::new(Vec::new()));
        let observed = Rc::clone(&measurements);
        tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
            &["fz", "compiler2", "pull", "product", "validation"],
            move |_, _, _, _, work| observed.borrow_mut().push(*work),
        );
        let types = crate::compiler2::Types::new();
        let mut memo = ProductMemo::default();
        let leaves = (1000..1000 + size).collect::<Vec<_>>();
        for leaf in &leaves {
            assert!(commit(&mut memo, member(*leaf), membership(&[])));
        }
        for ancestor in (0..size).rev() {
            let children = if ancestor + 1 == size {
                leaves.clone()
            } else {
                vec![ancestor + 1]
            };
            assert!(commit(&mut memo, member(ancestor), membership(&children)));
        }
        assert!(commit(&mut memo, packaging(), membership(&[])));
        memo.register_rooted(packaging(), member(0), &types);
        Rc::get_mut(&mut memo.produced.get_mut(&packaging()).unwrap().dependencies)
            .unwrap()
            .rooted_read = Some(RootedRead {
            position: 0,
            delivered: true,
            controls_delivered: true,
        });
        memo.rooted.get_mut(&packaging()).unwrap().dirty.clear();
        memo.rooted.get_mut(&packaging()).unwrap().changes.clear();
        memo.mutate_product_wave(
            &tel,
            leaves
                .iter()
                .map(|leaf| (ReaderMutation::Dirty, member(*leaf)))
                .collect(),
            &types,
        );
        measurements.borrow_mut().clear();
        assert_eq!(memo.stale_dependency(&tel, &packaging(), &types), None);
        let recorded = measurements.borrow();
        assert_eq!(recorded.len(), 1);
        let work = recorded[0];
        assert_eq!(work.vertex_visits, u64::from(size) + 1);
        assert_eq!(work.edge_scans, 0);
        assert_eq!(
            work.witness_visits,
            u64::from(size) * 2,
            "shared ancestry is walked once across all dirty leaves"
        );
        assert_eq!(work.mutation_pops, 0);
        assert!(
            work.ordering_comparisons <= u64::from(size) * u64::from(size.ilog2()) * 4,
            "deterministic owner ordering is bounded by sorting the dirty subset"
        );
        assert!(memo.dirty_descendants.is_empty());
        assert!(memo.rooted[&packaging()].dirty.is_empty());
    }
}

#[test]
fn an_independent_member_proof_does_not_clear_its_readers_stale_later_control() {
    let tel = ConfiguredTelemetry::new();
    let types = crate::compiler2::Types::new();
    let mut memo = ProductMemo::default();
    for key in [member(0), member(1)] {
        assert!(commit(&mut memo, key, membership(&[])));
    }
    let dependencies = ProductDependencies {
        products: IndexMap::from([(member(1), Some(1))]),
        ..ProductDependencies::default()
    };
    assert!(commit(&mut memo, packaging(), dependencies));
    memo.register_rooted(packaging(), member(0), &types);
    Rc::get_mut(&mut memo.produced.get_mut(&packaging()).unwrap().dependencies)
        .unwrap()
        .rooted_read = Some(RootedRead {
        position: 0,
        delivered: true,
        controls_delivered: true,
    });
    memo.rooted.get_mut(&packaging()).unwrap().dirty.clear();
    memo.rooted.get_mut(&packaging()).unwrap().changes.clear();
    memo.observed_products.extend([packaging(), member(0)]);
    memo.mutate_product_wave(&tel, vec![(ReaderMutation::Dirty, member(0))], &types);
    memo.invalidate_products(&tel, [member(1)], &types);
    memo.external_changes.clear();
    assert_eq!(memo.stale_dependency(&tel, &packaging(), &types), Some(member(1)));
    assert!(
        !memo.dirty_descendants.contains(&member(0)),
        "independent complete proof is accepted"
    );
    assert!(
        memo.dirty_descendants.contains(&packaging()),
        "later failed control keeps its reader dirty"
    );
    assert!(
        memo.external_changes
            .iter()
            .any(|change| change.key == member(0) && change.new_settled)
    );
    assert!(
        !memo
            .external_changes
            .iter()
            .any(|change| change.key == packaging() && change.new_settled)
    );
    assert!(commit(&mut memo, member(1), membership(&[])));
    assert_eq!(memo.stale_dependency(&tel, &packaging(), &types), None);
    assert!(memo.external_state(&packaging()).settled);
}

#[test]
fn a_mixed_membership_and_value_cycle_validates_equal_observations_together() {
    let tel = ConfiguredTelemetry::new();
    let types = crate::compiler2::Types::new();
    let mut memo = ProductMemo::default();
    assert!(commit(&mut memo, packaging(), membership(&[])));
    let mut dependency = membership(&[]);
    dependency.products.insert(packaging(), memo.generation(&packaging()));
    assert!(commit(&mut memo, member(0), dependency));
    memo.register_rooted(packaging(), member(0), &types);
    Rc::get_mut(&mut memo.produced.get_mut(&packaging()).unwrap().dependencies)
        .unwrap()
        .rooted_read = Some(RootedRead {
        position: 0,
        delivered: true,
        controls_delivered: true,
    });
    let root = memo.rooted.get_mut(&packaging()).unwrap();
    root.dirty.clear();
    root.changes.clear();
    memo.mutate_product_wave(&tel, vec![(ReaderMutation::Dirty, member(0))], &types);
    let mut visiting = ProductValidationWalk::default();
    let stale = memo.stale_dependency_inner(&tel, &packaging(), &mut visiting, &types, true);
    assert_eq!(stale, None, "dirty state alone is not changed evidence");
    assert_eq!(
        visiting.checked,
        HashSet::from([packaging(), member(0)]),
        "both sides of the cycle must be validated"
    );
    assert_eq!(memo.stale_dependency(&tel, &packaging(), &types), None);
    assert!(memo.dirty_descendants.is_empty());
    assert!(memo.rooted[&packaging()].dirty.is_empty());
    assert_eq!(memo.generation(&packaging()), Some(1));
    assert_eq!(memo.generation(&member(0)), Some(1));
}
