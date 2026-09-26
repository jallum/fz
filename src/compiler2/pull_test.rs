include!("pull/ownership_test.rs");
include!("pull/mutation_test.rs");
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;

use crate::telemetry::causal::{
    CausalReport, ProductEvaluationCause, ProductEvaluationTriggerKind, ProductEvaluationWait, parse_public_trace,
};
use crate::telemetry::{ConfiguredTelemetry, JsonlBackend};

use super::super::artifact::{
    CallEdge, CallReturnFlow, CallTarget, DirectCallEdge, MaterializedCallEdge, MaterializedExecutable,
    MaterializedExecutableTransport,
};
use super::super::body::{ControlEntryId, ControlEntryOrigin, LoweredClause, LoweredEntry, LoweredStep, LoweredTail};
use super::super::facts::FactReadiness;
use super::super::identity::{ExecutableNeed, FunctionId};
use super::super::transport::{BoundaryFacts, BoundaryId, CallableFacts, CallableId, ExecutableSymbol};
use super::*;

fn prospective_dependency(dependency: &ProductKey) -> ProductDependencies {
    ProductDependencies {
        rooted_read: None,
        membership: HashSet::new(),
        products: IndexMap::from([(dependency.clone(), None)]),
        facts: HashMap::new(),
    }
}

fn finish_test_entry(
    memo: &mut ProductMemo,
    tel: &impl Telemetry,
    key: &ProductKey,
    value: ProductValue,
    dependencies: ProductDependencies,
    types: &super::super::types::Types,
) -> bool {
    memo.finish_completion(
        tel,
        causal_product_events_enabled(tel),
        key,
        ProductCompletion::Single(value, dependencies),
        types,
    )
}

fn finish_test_group(
    memo: &mut ProductMemo,
    tel: &impl Telemetry,
    requested: &ProductKey,
    members: Vec<(ProductKey, ProductValue, ProductDependencies)>,
    types: &super::super::types::Types,
) -> bool {
    memo.finish_completion(
        tel,
        causal_product_events_enabled(tel),
        requested,
        ProductCompletion::RecursiveGroup(members),
        types,
    )
}

fn retained_test_session(root: RootId, fact: &FactKey, types: &super::super::types::Types) -> PullSession {
    let tel = ConfiguredTelemetry::new();
    let mut session = PullSession::new(root);
    let key = ProductKey::RootBackendProduct(root);
    assert!(finish_test_entry(
        &mut session.memo,
        &tel,
        &key,
        ProductValue::Unit,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::new(),
            facts: HashMap::from([(
                FactUse::settled(fact.clone()),
                FactState {
                    revision: Some(1),
                    settled: true,
                },
            )]),
        },
        types,
    ));
    session
}

#[test]
fn retiring_a_never_produced_observed_product_preserves_its_pending_demand() {
    use super::super::scheduler::Scheduler;

    let types = fake_types();
    let root = RootId::for_test(1);
    let address = ProductAddress {
        root,
        key: ProductKey::RootBackendProduct(root),
    };
    let mut sessions = ProductSessions::default();
    sessions.observe(&address);
    let mut scheduler = Scheduler::new();
    scheduler.complete_ordered_with_external(
        &super::super::Job::SeedRoot(root),
        crate::compiler2::scheduler::CompletionEffects::single(
            crate::compiler2::drive::Derivation::of(
                super::super::Job::SeedRoot(root),
                crate::compiler2::drive::DerivationKey::Job,
            ),
            HashSet::new(),
            HashSet::from([FactUse::current(DependencyKey::Product(address.clone()))]),
            Vec::new(),
            Vec::new(),
        ),
        &sessions,
        &types,
    );
    assert_eq!(sessions.next_request(), Some(address.clone()));
    sessions.retry_request(address.clone());
    let withdrawal = sessions.retirement_changes(root);
    assert!(sessions.retire(root, &types));
    scheduler.apply_external_changes_ordered(withdrawal, &sessions, &types);
    assert_eq!(
        scheduler.pending_jobs(),
        0,
        "missing-to-missing withdrawal does not wake the standing waiter"
    );
    assert!(scheduler.has_dependency_consumers(&DependencyKey::Product(address.clone())));
    assert!(
        sessions.get(root).is_none(),
        "retirement must release the memo before any later drive"
    );
    assert_eq!(
        sessions.next_request(),
        Some(address.clone()),
        "an unchanged missing state cannot wake the standing scheduler waiter; its original demand must survive"
    );
    assert!(
        sessions
            .get(root)
            .unwrap()
            .memo
            .observed_products
            .contains(&address.key)
    );
    assert!(
        sessions.next_request().is_none(),
        "retirement must not duplicate the already queued failed demand"
    );
    sessions.unobserve(&address);
    sessions.retry_request(address);
    assert!(
        sessions.next_request().is_none(),
        "detaching the actual scheduler consumer cancels demand"
    );
}

#[test]
fn renewed_product_demand_does_not_revive_duplicate_stale_queue_entries() {
    let root = RootId::for_test(1);
    let address = ProductAddress {
        root,
        key: ProductKey::RootBackendProduct(root),
    };
    let mut sessions = ProductSessions::default();
    sessions.observe(&address);
    sessions.unobserve(&address);
    sessions.observe(&address);
    assert!(sessions.retire(root, &fake_types()));
    assert_eq!(sessions.next_request(), Some(address));
    assert!(
        sessions.next_request().is_none(),
        "renewed demand must not turn stale queue entries into duplicate validations"
    );
}

#[test]
fn retained_session_broker_fans_runtime_demand_movement_to_dormant_and_nested_active_roots_once() {
    let types = fake_types();
    let fact = FactKey::RuntimeDemand(fake_executable_with_function(RootId::for_test(99), 99));
    let left = RootId::for_test(1);
    let right = RootId::for_test(2);
    let dormant = RootId::for_test(3);
    let mut sessions = ProductSessions::default();
    for session in [
        retained_test_session(left, &fact, &types),
        retained_test_session(right, &fact, &types),
        retained_test_session(dormant, &fact, &types),
    ] {
        let root = session.root();
        sessions.active_roots.insert(root, ActiveRootProduct::default());
        let session = Rc::new(RefCell::new(session));
        sessions.sessions.insert(root, Rc::clone(&session));
        sessions.restore(session);
    }
    assert_eq!(sessions.counts(), (3, 3));

    let (active_left, _) = sessions.take(left, WorkStartTally::default());
    let (active_right, _) = sessions.take(right, WorkStartTally::default());
    let tel = ConfiguredTelemetry::new();
    sessions.publish(
        &tel,
        &types,
        &[FactMovement {
            key: fact.clone(),
            state: FactState {
                revision: Some(2),
                settled: false,
            },
        }],
    );
    sessions.publish(
        &tel,
        &types,
        &[FactMovement {
            key: fact.clone(),
            state: FactState {
                revision: Some(2),
                settled: true,
            },
        }],
    );
    sessions.drain_active_movements(left, &mut active_left.borrow_mut());
    sessions.drain_active_movements(right, &mut active_right.borrow_mut());
    let final_state = FactState {
        revision: Some(2),
        settled: true,
    };
    assert_eq!(
        active_left.borrow().pending_fact_states,
        HashMap::from([(fact.clone(), final_state)])
    );
    assert_eq!(
        active_right.borrow().pending_fact_states,
        HashMap::from([(fact.clone(), final_state)])
    );
    assert_eq!(
        sessions.sessions[&dormant].borrow().pending_fact_states,
        HashMap::from([(fact.clone(), final_state)])
    );
    sessions.finish_activation(right, &mut active_right.borrow_mut(), WorkStartTally::default());
    sessions.restore(active_right);
    sessions.finish_activation(left, &mut active_left.borrow_mut(), WorkStartTally::default());
    sessions.restore(active_left);

    assert!(sessions.retire(left, &types));
    assert_eq!(sessions.counts(), (2, 2));
    assert_eq!(sessions.roots_by_fact[&fact], HashSet::from([right, dormant]));
}

#[test]
fn equal_fact_delivery_keeps_both_retained_root_products_settled() {
    let types = fake_types();
    let tel = ConfiguredTelemetry::new();
    let fact = FactKey::RootEntry(RootId::for_test(99));
    let roots = [RootId::for_test(1), RootId::for_test(2)];
    let mut sessions = ProductSessions::default();
    for root in roots {
        let session = retained_test_session(root, &fact, &types);
        sessions.active_roots.insert(root, ActiveRootProduct::default());
        let session = Rc::new(RefCell::new(session));
        sessions.sessions.insert(root, Rc::clone(&session));
        sessions.restore(session);
    }
    sessions.publish(
        &tel,
        &types,
        &[FactMovement {
            key: fact,
            state: FactState {
                revision: Some(1),
                settled: true,
            },
        }],
    );
    for root in roots {
        let mut session = sessions.sessions.get(&root).expect("retained root").borrow_mut();
        session.reconcile_fact_movements(&tel, &types);
        assert!(session.memo.get(&ProductKey::RootBackendProduct(root)).is_some());
    }
}

/// Recursive search work is a property of the pending graph, not of the
/// fresh `RandomState` assigned to each memo. The side branch made the old
/// early-exit gate visit a variable prefix before its repeated component
/// scans. One traversal must inspect each reachable vertex and edge once.
#[test]
fn recursive_group_search_work_is_a_function_of_the_pending_graph() {
    let types = fake_types();
    let root = RootId::for_test(81);
    let callable = |function, value| {
        ProductKey::CallableConstruction(TransportPosition::Value {
            executable: executable_symbol_for_test(&fake_executable_with_function(root, function)),
            value: ValueId::from_u32(value),
        })
    };
    let current = callable(810, 0);
    let target = callable(811, 1);
    let detour_1 = callable(812, 2);
    let detour_2 = callable(813, 3);
    let detour_3 = callable(814, 4);

    for _ in 0..32 {
        let mut memo = ProductMemo::default();
        for (key, dependencies) in [
            (
                target.clone(),
                ProductDependencies {
                    rooted_read: None,
                    membership: HashSet::new(),
                    products: IndexMap::from([(current.clone(), None), (detour_1.clone(), None)]),
                    facts: HashMap::new(),
                },
            ),
            (
                detour_1.clone(),
                ProductDependencies {
                    rooted_read: None,
                    membership: HashSet::new(),
                    products: IndexMap::from([(detour_2.clone(), None)]),
                    facts: HashMap::new(),
                },
            ),
            (
                detour_2.clone(),
                ProductDependencies {
                    rooted_read: None,
                    membership: HashSet::new(),
                    products: IndexMap::from([(detour_3.clone(), None)]),
                    facts: HashMap::new(),
                },
            ),
            (detour_3.clone(), ProductDependencies::default()),
        ] {
            memo.unblock(ProductRequestId(NonZeroU64::MIN), &key, dependencies);
        }

        let (members, search) =
            memo.pending_strong_component(&current, &prospective_dependency(&target), &target, &types);
        assert_eq!(
            members.map(|members| members.into_iter().collect::<HashSet<_>>()),
            Some(HashSet::from([current.clone(), target.clone()]))
        );
        assert_eq!(
            search,
            RecursiveGroupSearch {
                candidate_inventory: 5,
                vertex_visits: 5,
                edge_scans: 5,
                cycle_closed: true,
                group_members: 2,
            }
        );
    }
}

#[test]
fn recursive_group_search_matches_pending_graph_boundaries() {
    let types = fake_types();
    let root = RootId::for_test(84);
    let current = ProductKey::AbiExecutable(fake_executable_with_function(root, 840));
    let dependency = ProductKey::AbiExecutable(fake_executable_with_function(root, 841));
    let peer = ProductKey::AbiExecutable(fake_executable_with_function(root, 842));
    let bridge = ProductKey::RootBackendProduct(root);
    let missing = ProductMemo::default();
    assert_eq!(
        missing.pending_strong_component(&current, &prospective_dependency(&dependency), &dependency, &types),
        (
            None,
            RecursiveGroupSearch {
                candidate_inventory: 0,
                vertex_visits: 0,
                edge_scans: 0,
                cycle_closed: false,
                group_members: 0,
            }
        )
    );

    let mut displaced = ProductMemo::default();
    finish_test_product(&mut displaced, &dependency, ProductValue::Unit, [current.clone()]);
    displaced.remove(&ConfiguredTelemetry::new(), &dependency, &types);
    assert_eq!(
        displaced.pending_strong_component(&current, &prospective_dependency(&dependency), &dependency, &types,),
        (
            None,
            RecursiveGroupSearch {
                candidate_inventory: 0,
                vertex_visits: 0,
                edge_scans: 0,
                cycle_closed: false,
                group_members: 0,
            }
        ),
        "a displaced product's last settled dependencies are not pending cycle evidence"
    );

    let mut self_cycle = ProductMemo::default();
    self_cycle.unblock(
        ProductRequestId(NonZeroU64::MIN),
        &current,
        ProductDependencies::default(),
    );
    assert_eq!(
        self_cycle.pending_strong_component(&current, &prospective_dependency(&current), &current, &types),
        (
            Some(vec![current.clone()]),
            RecursiveGroupSearch {
                candidate_inventory: 1,
                vertex_visits: 1,
                edge_scans: 1,
                cycle_closed: true,
                group_members: 1,
            }
        )
    );

    let mut disjoint = ProductMemo::default();
    disjoint.unblock(
        ProductRequestId(NonZeroU64::MIN),
        &dependency,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::from([(peer.clone(), None)]),
            facts: HashMap::new(),
        },
    );
    disjoint.unblock(
        ProductRequestId(NonZeroU64::MIN),
        &peer,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::from([(dependency.clone(), None)]),
            facts: HashMap::new(),
        },
    );
    assert_eq!(
        disjoint.pending_strong_component(&current, &prospective_dependency(&dependency), &dependency, &types,),
        (
            None,
            RecursiveGroupSearch {
                candidate_inventory: 2,
                vertex_visits: 2,
                edge_scans: 2,
                cycle_closed: false,
                group_members: 0,
            }
        )
    );

    let mut cross_kind = ProductMemo::default();
    cross_kind.unblock(
        ProductRequestId(NonZeroU64::MIN),
        &dependency,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::from([(bridge.clone(), None)]),
            facts: HashMap::new(),
        },
    );
    cross_kind.unblock(
        ProductRequestId(NonZeroU64::MIN),
        &bridge,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::from([(current.clone(), None)]),
            facts: HashMap::new(),
        },
    );
    let (members, search) =
        cross_kind.pending_strong_component(&current, &prospective_dependency(&dependency), &dependency, &types);
    assert_eq!(
        members.map(|members| members.into_iter().collect::<HashSet<_>>()),
        Some(HashSet::from([current.clone(), dependency.clone()]))
    );
    assert_eq!(
        search,
        RecursiveGroupSearch {
            candidate_inventory: 2,
            vertex_visits: 3,
            edge_scans: 3,
            cycle_closed: true,
            group_members: 2,
        }
    );
}

#[test]
fn recursive_reads_record_exact_dependency_generation_on_every_outcome() {
    let tel = ConfiguredTelemetry::new();
    let types = fake_types();
    let root = RootId::for_test(85);
    let current = ProductKey::AbiExecutable(fake_executable_with_function(root, 850));
    let missing = ProductKey::AbiExecutable(fake_executable_with_function(root, 851));
    let ready = ProductKey::AbiExecutable(fake_executable_with_function(root, 852));
    let cyclic = ProductKey::AbiExecutable(fake_executable_with_function(root, 853));
    let mut session = PullSession::new(root);

    {
        let mut context = ProductReadContext::new(&mut session);
        assert!(matches!(
            context.read_recursive_product(&tel, missing.clone(), &current, &types),
            RecursiveProductRead::Waiting
        ));
        assert_eq!(context.dependencies.products.get(&missing), Some(&None));
    }

    finish_test_product(&mut session.memo, &ready, ProductValue::Unit, []);
    assert_eq!(
        session
            .memo
            .pending_strong_component(&current, &prospective_dependency(&ready), &ready, &types),
        (
            None,
            RecursiveGroupSearch {
                candidate_inventory: 0,
                vertex_visits: 0,
                edge_scans: 0,
                cycle_closed: false,
                group_members: 0,
            }
        )
    );
    {
        let mut context = ProductReadContext::new(&mut session);
        assert!(matches!(
            context.read_recursive_product(&tel, ready.clone(), &current, &types),
            RecursiveProductRead::Ready(ProductValue::Unit)
        ));
        assert_eq!(context.dependencies.products.get(&ready), Some(&Some(1)));
    }

    session.memo.unblock(
        ProductRequestId(NonZeroU64::MIN),
        &cyclic,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::from([(current.clone(), None)]),
            facts: HashMap::new(),
        },
    );
    let mut context = ProductReadContext::new(&mut session);
    let RecursiveProductRead::Group(members) = context.read_recursive_product(&tel, cyclic.clone(), &current, &types)
    else {
        panic!("the prospective edge should close the pending cycle");
    };
    assert_eq!(
        members.into_iter().collect::<HashSet<_>>(),
        HashSet::from([current, cyclic.clone()])
    );
    assert_eq!(context.dependencies.products.get(&cyclic), Some(&None));
}

fn fact_movement(key: FactKey, revision: Option<u64>, settled: bool) -> FactMovement<FactKey> {
    FactMovement {
        key,
        state: FactState { revision, settled },
    }
}

struct ProductTelemetryCapture {
    produced: Rc<Cell<u64>>,
    cache_hits: Rc<Cell<u64>>,
}

impl ProductTelemetryCapture {
    fn install(telemetry: &ConfiguredTelemetry) -> Self {
        let capture = Self {
            produced: Rc::new(Cell::new(0)),
            cache_hits: Rc::new(Cell::new(0)),
        };
        let cache_hits = Rc::clone(&capture.cache_hits);
        telemetry.attach_raw_event1::<ProductKey, _>(
            &["fz", "compiler2", "pull", "product", "cache_hit"],
            move |_, _, _, _| cache_hits.set(cache_hits.get() + 1),
        );
        let produced = Rc::clone(&capture.produced);
        telemetry.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
            &["fz", "compiler2", "pull", "product", "settled"],
            move |_, _, _, _, _, _| produced.set(produced.get() + 1),
        );
        capture
    }
}

#[test]
fn recursive_group_commits_one_semantic_sequence_for_every_requested_anchor() {
    let root = RootId::for_test(88);
    let mut types = super::super::Types::new();
    let keys =
        [880, 881, 882].map(|function| ProductKey::AbiExecutable(fake_executable_in(&mut types, root, function)));
    let mut expected = keys.to_vec();
    sort_product_keys(&mut expected, &types);

    for requested in &keys {
        for reverse in [false, true] {
            let tel = ConfiguredTelemetry::new();
            let observed = Rc::new(RefCell::new(Vec::new()));
            let sink = Rc::clone(&observed);
            tel.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
                &["fz", "compiler2", "pull", "product", "settled"],
                move |_, _, _, key, _, settlement| sink.borrow_mut().push((key.clone(), settlement.group)),
            );
            let mut order = keys.to_vec();
            if reverse {
                order.reverse();
            }
            let entries = order
                .into_iter()
                .map(|key| (key, ProductValue::Unit, ProductDependencies::default()))
                .collect();
            let mut memo = ProductMemo::default();
            for key in &keys {
                assert!(memo.begin(key.clone()));
            }
            assert!(finish_test_group(&mut memo, &tel, requested, entries, &types));
            let observed = observed.borrow();
            assert_eq!(
                observed.iter().map(|(key, _)| key.clone()).collect::<Vec<_>>(),
                expected
            );
            let groups = observed.iter().map(|(_, group)| *group).collect::<HashSet<_>>();
            assert_eq!(groups.len(), 1);
            assert!(!groups.contains(&None));
        }
    }
}

#[test]
fn changed_group_drains_produced_and_pending_reader_diamond_in_semantic_order() {
    let root = RootId::for_test(87);
    let mut types = super::super::Types::new();
    let keys = [870, 871, 872, 873, 874, 875, 876]
        .map(|function| ProductKey::AbiExecutable(fake_executable_in(&mut types, root, function)));
    let [left, right, left_reader, right_reader, join, pending, pending_child] = &keys;
    let mut expected_displaced = vec![left_reader.clone(), right_reader.clone()];
    sort_product_keys(&mut expected_displaced, &types);

    for reverse in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let mut memo = ProductMemo::default();
        let mut sources = vec![left.clone(), right.clone()];
        if reverse {
            sources.reverse();
        }
        for source in &sources {
            finish_test_product(&mut memo, source, ProductValue::Unit, []);
        }
        finish_test_product(&mut memo, left_reader, ProductValue::Unit, [left.clone()]);
        finish_test_product(&mut memo, right_reader, ProductValue::Unit, [right.clone()]);
        finish_test_product(
            &mut memo,
            join,
            ProductValue::Unit,
            [left_reader.clone(), right_reader.clone()],
        );
        memo.unblock(
            ProductRequestId(NonZeroU64::MIN),
            pending,
            ProductDependencies {
                rooted_read: None,
                membership: HashSet::new(),
                products: IndexMap::from([
                    (left.clone(), memo.generation(left)),
                    (right.clone(), memo.generation(right)),
                ]),
                facts: HashMap::new(),
            },
        );
        memo.unblock(
            ProductRequestId(NonZeroU64::MIN),
            pending_child,
            ProductDependencies {
                rooted_read: None,
                membership: HashSet::new(),
                products: IndexMap::from([(pending.clone(), None)]),
                facts: HashMap::new(),
            },
        );

        let displaced = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&displaced);
        tel.attach_raw_event1::<ProductKey, _>(
            &["fz", "compiler2", "pull", "product", "displaced"],
            move |_, _, _, key| sink.borrow_mut().push(key.clone()),
        );
        let replacement = ProductValue::ExecutableEffects(EffectSummary::default());
        let entries = sources
            .iter()
            .cloned()
            .map(|key| (key, replacement.clone(), ProductDependencies::default()))
            .collect();
        assert!(finish_test_group(&mut memo, &tel, left, entries, &types));

        assert_eq!(*displaced.borrow(), expected_displaced);
        assert!(memo.get(join).is_some());
        assert!(memo.dirty_descendants.contains(join));
        assert!(!memo.pending_dependencies.contains_key(pending));
        assert!(!memo.pending_dependencies.contains_key(pending_child));
    }
}

#[test]
fn transitive_dirtiness_retracts_pending_readers_but_leaves_settled_readers_lazy() {
    let tel = ConfiguredTelemetry::new();
    let types = fake_types();
    let root = RootId::for_test(99);
    let source = ProductKey::AbiExecutable(fake_executable_with_function(root, 990));
    let intermediate = ProductKey::AbiExecutable(fake_executable_with_function(root, 991));
    let pending = ProductKey::AbiExecutable(fake_executable_with_function(root, 992));
    let settled = ProductKey::AbiExecutable(fake_executable_with_function(root, 993));
    let mut memo = ProductMemo::default();
    finish_test_product(&mut memo, &source, ProductValue::Unit, []);
    finish_test_product(&mut memo, &intermediate, ProductValue::Unit, [source.clone()]);
    memo.unblock(
        ProductRequestId(NonZeroU64::MIN),
        &pending,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::from([(intermediate.clone(), Some(1))]),
            facts: HashMap::new(),
        },
    );
    finish_test_product(&mut memo, &settled, ProductValue::Unit, [intermediate.clone()]);

    memo.remove(&tel, &source, &types);

    assert!(!memo.pending_dependencies.contains_key(&pending));
    assert!(memo.get(&settled).is_some());
    assert!(memo.dirty_descendants.contains(&intermediate));
    assert!(memo.dirty_descendants.contains(&settled));
}

#[derive(Default)]
struct FakeProducers {
    types: super::super::Types,
    produced: HashSet<ProductKey>,
    calls: Vec<ProductKey>,
    self_wait: Option<ProductKey>,
    root_entry: Option<ExecutableKey>,
    root_prerequisites: Vec<ProductKey>,
    root_recursive_prerequisite: Option<ProductKey>,
    recursive_telemetry: Option<Rc<ConfiguredTelemetry>>,
    facts: HashMap<FactKey, FactState>,
    runtime_fact: Option<FactUse<FactKey>>,
    runtime_value: Option<ProductValue>,
    runtime_children: HashMap<ProductKey, ProductKey>,
    materialized_value: Option<ProductValue>,
    backend_fact: Option<FactUse<FactKey>>,
    backend_value: Option<ProductValue>,
    fact_state_reads: usize,
    fail_native_once: bool,
    native_fact: Option<FactUse<FactKey>>,
}

impl FakeProducers {
    fn fact_state(&mut self, fact: &FactUse<FactKey>) -> FactState {
        self.fact_state_reads += 1;
        self.facts.get(fact.fact()).copied().unwrap_or(FactState {
            revision: None,
            settled: false,
        })
    }

    fn produce_unit(&mut self, key: ProductKey) -> PullOutcome {
        self.calls.push(key.clone());
        self.produced.insert(key);
        PullOutcome::Produced(ProductValue::Unit)
    }
}

impl ProductProducers for FakeProducers {
    fn product_types(&self) -> &super::super::Types {
        &self.types
    }

    fn produce(&mut self, context: &mut ProductReadContext<'_>, key: &ProductKey) -> PullOutcome {
        if self.self_wait.as_ref() == Some(key) {
            self.calls.push(key.clone());
            return PullOutcome::wait_on_product(key.clone());
        }
        match key {
            ProductKey::RootBackendProduct(root) => {
                let tel = ConfiguredTelemetry::new();
                self.calls.push(key.clone());
                let mut waits = self
                    .root_prerequisites
                    .iter()
                    .filter(|prerequisite| {
                        context
                            .read_product_entry(&tel, (*prerequisite).clone(), &self.types)
                            .is_none()
                    })
                    .cloned()
                    .map(PullWait::Product)
                    .collect::<Vec<_>>();
                if let Some(prerequisite) = self.root_recursive_prerequisite.clone() {
                    let telemetry = self
                        .recursive_telemetry
                        .as_ref()
                        .expect("a recursive fake producer needs its driver telemetry");
                    if matches!(
                        context.read_recursive_product(telemetry.as_ref(), prerequisite.clone(), key, &self.types,),
                        RecursiveProductRead::Waiting
                    ) {
                        waits.push(PullWait::Product(prerequisite));
                    }
                }
                if !waits.is_empty() {
                    return PullOutcome::Waiting(waits);
                }
                let prerequisite =
                    ProductKey::AbiExecutable(self.root_entry.clone().expect("fake root entry should be set"));
                if context
                    .read_product_entry(&tel, prerequisite.clone(), &self.types)
                    .is_some()
                {
                    self.produced.insert(ProductKey::RootBackendProduct(*root));
                    PullOutcome::Produced(ProductValue::Unit)
                } else {
                    PullOutcome::wait_on_product(prerequisite)
                }
            }
            ProductKey::NativeProgram(_) => {
                self.calls.push(key.clone());
                if let Some(fact) = self.native_fact.clone() {
                    let state = self.fact_state(&fact);
                    context.record_fact_state(fact.clone(), state);
                    if !state.settled {
                        return PullOutcome::wait_on_fact(fact);
                    }
                }
                if std::mem::take(&mut self.fail_native_once) {
                    PullOutcome::Failed
                } else {
                    PullOutcome::Produced(ProductValue::Unit)
                }
            }
            ProductKey::BackendExecutable(_) => {
                self.calls.push(key.clone());
                if let Some(fact) = self.backend_fact.clone() {
                    let state = self.fact_state(&fact);
                    let ready = match fact.readiness() {
                        FactReadiness::Current => state.revision.is_some(),
                        FactReadiness::Settled => state.settled,
                    };
                    context.record_fact_state(fact.clone(), state);
                    if !ready {
                        return PullOutcome::wait_on_fact(fact);
                    }
                } else if self.backend_value.is_none() {
                    return PullOutcome::wait_on_fact(FactUse::current(FactKey::CodeIndexed(
                        super::super::SourceOwner::for_test(0),
                    )));
                }
                self.produced.insert(key.clone());
                PullOutcome::Produced(self.backend_value.clone().unwrap_or(ProductValue::Unit))
            }
            ProductKey::MaterializedExecutable(_) => {
                self.calls.push(key.clone());
                self.produced.insert(key.clone());
                PullOutcome::Produced(self.materialized_value.clone().unwrap_or(ProductValue::Unit))
            }
            ProductKey::AbiExecutable(_) => {
                self.calls.push(key.clone());
                if let Some(fact) = self.runtime_fact.clone() {
                    let state = self.fact_state(&fact);
                    let ready = match fact.readiness() {
                        FactReadiness::Current => state.revision.is_some(),
                        FactReadiness::Settled => state.settled,
                    };
                    context.record_fact_state(fact.clone(), state);
                    if !ready {
                        return PullOutcome::wait_on_fact(fact);
                    }
                }
                if let Some(child) = self.runtime_children.get(key).cloned()
                    && context
                        .read_product_entry(&ConfiguredTelemetry::new(), child.clone(), &self.types)
                        .is_none()
                {
                    return PullOutcome::wait_on_product(child);
                }
                self.produced.insert(key.clone());
                PullOutcome::Produced(self.runtime_value.clone().unwrap_or(ProductValue::Unit))
            }
            _ => self.produce_unit(key.clone()),
        }
    }
}

#[test]
fn failed_product_is_not_memoized_and_can_be_retried() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(0);
    let key = ProductKey::NativeProgram(root);
    let prerequisite = FactUse::settled(FactKey::RootEntry(root));
    let mut producers = FakeProducers {
        fail_native_once: true,
        native_fact: Some(prerequisite.clone()),
        ..FakeProducers::default()
    };
    let mut driver = ProductDriver::new(&tel, root);

    assert_eq!(
        driver.pull(&mut producers, key.clone()),
        PullOutcome::wait_on_fact(prerequisite.clone())
    );
    assert!(driver.session().memo.pending_product_dependencies(&key).is_some());
    producers.facts.insert(
        prerequisite.fact().clone(),
        FactState {
            revision: Some(1),
            settled: true,
        },
    );
    assert_eq!(driver.pull(&mut producers, key.clone()), PullOutcome::Failed);
    assert!(!driver.session().memo.contains_in_progress(&key));
    assert!(driver.session().memo.pending_product_dependencies(&key).is_none());
    assert_eq!(driver.session().memo.get(&key), None);
    assert_eq!(driver.session().memo.generation(&key), None);

    assert_eq!(
        driver.pull(&mut producers, key.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(driver.session().memo.generation(&key), Some(1));
}

#[test]
fn equal_root_reproduction_retains_root_allocation_and_native_generation() {
    let root = RootId::for_test(0);
    let root_key = ProductKey::RootBackendProduct(root);
    let native_key = ProductKey::NativeProgram(root);
    let backend = Rc::new(super::super::artifact::BackendProgram::empty_for_test());
    let mut memo = ProductMemo::default();
    finish_test_product(
        &mut memo,
        &root_key,
        ProductValue::RootBackendProduct(Rc::clone(&backend)),
        [],
    );
    finish_test_product(&mut memo, &native_key, ProductValue::Unit, [root_key.clone()]);
    let generation = memo.generation(&root_key);
    let native_generation = memo.generation(&native_key);
    finish_test_product(
        &mut memo,
        &root_key,
        ProductValue::RootBackendProduct(Rc::new((*backend).clone())),
        [],
    );
    let Some(ProductValue::RootBackendProduct(reproduced)) = memo.get(&root_key) else {
        panic!("retained root");
    };
    assert!(Rc::ptr_eq(&backend, reproduced));
    assert_eq!(memo.generation(&root_key), generation);
    assert!(memo.get(&native_key).is_some());
    assert_eq!(memo.generation(&native_key), native_generation);
}

#[test]
fn equal_native_reproduction_retains_allocation_and_generation() {
    let root = RootId::for_test(0);
    let key = ProductKey::NativeProgram(root);
    let native = || NativeProgram {
        entry: crate::fz_ir::FnId(0),
        module: crate::fz_ir::Module::default(),
        executable_entries: Vec::new(),
        bodies: Vec::new(),
        callable_boundaries: Vec::new(),
    };
    let original = Rc::new(native());
    let mut memo = ProductMemo::default();

    finish_test_product(&mut memo, &key, ProductValue::NativeProgram(Rc::clone(&original)), []);
    let generation = memo.generation(&key);
    finish_test_product(&mut memo, &key, ProductValue::NativeProgram(Rc::new(native())), []);

    let Some(ProductValue::NativeProgram(retained)) = memo.get(&key) else {
        panic!("native program must remain settled");
    };
    assert!(Rc::ptr_eq(retained, &original));
    assert_eq!(memo.generation(&key), generation);
}

#[test]
fn product_driver_names_prerequisites_without_follow_up_jobs() {
    let tel = ConfiguredTelemetry::new();
    let capture = ProductTelemetryCapture::install(&tel);
    let root = RootId::for_test(0);
    let executable = fake_executable(root);
    let root_key = ProductKey::RootBackendProduct(root);
    let prerequisite = ProductKey::AbiExecutable(executable.clone());
    let mut producers = FakeProducers {
        root_entry: Some(executable),
        ..FakeProducers::default()
    };
    let mut driver = ProductDriver::new(&tel, root);

    let first = driver.pull(&mut producers, root_key.clone());
    assert_eq!(first, PullOutcome::wait_on_product(prerequisite.clone()));
    assert_eq!(
        driver.pull(&mut producers, prerequisite),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        driver.pull(&mut producers, root_key.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        driver.pull(&mut producers, root_key.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );

    assert_eq!(producers.calls.iter().filter(|key| **key == root_key).count(), 2);
    assert_eq!(capture.produced.get(), 2);
    assert_eq!(capture.cache_hits.get(), 1);
}

#[test]
fn product_driver_correlates_waiting_producer_runs_and_cache_hits() {
    let tel = Rc::new(ConfiguredTelemetry::new());
    let (buf, writer) = crate::telemetry::capture::vec_writer();
    JsonlBackend::new_writer(writer).install(tel.as_ref());
    let root = RootId::for_test(90);
    let root_key = ProductKey::RootBackendProduct(root);
    let dependency = ProductKey::AbiExecutable(fake_executable_with_function(root, 901));
    let dependency_child = ProductKey::AbiExecutable(fake_executable_with_function(root, 902));
    let moved = ProductKey::AbiExecutable(fake_executable_with_function(root, 903));
    let mut producers = FakeProducers {
        root_entry: match &dependency {
            ProductKey::AbiExecutable(executable) => Some(executable.clone()),
            _ => unreachable!(),
        },
        root_prerequisites: vec![moved.clone()],
        root_recursive_prerequisite: Some(dependency.clone()),
        recursive_telemetry: Some(Rc::clone(&tel)),
        runtime_children: HashMap::from([(dependency.clone(), dependency_child.clone())]),
        ..FakeProducers::default()
    };
    let mut driver = ProductDriver::new(tel.as_ref(), root);

    assert_eq!(
        driver.pull(&mut producers, dependency.clone()),
        PullOutcome::wait_on_product(dependency_child.clone())
    );
    assert_eq!(
        driver.pull(&mut producers, root_key.clone()),
        PullOutcome::Waiting(vec![
            PullWait::Product(moved.clone()),
            PullWait::Product(dependency.clone())
        ])
    );
    assert_eq!(
        driver.pull(&mut producers, moved),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        driver.pull(&mut producers, root_key.clone()),
        PullOutcome::wait_on_product(dependency.clone())
    );
    assert_eq!(
        driver.pull(&mut producers, dependency_child),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        driver.pull(&mut producers, dependency),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        driver.pull(&mut producers, root_key.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        driver.pull(&mut producers, root_key),
        PullOutcome::Produced(ProductValue::Unit)
    );
    driver.finish_session();

    let events = parse_public_trace(&buf.borrow());
    let requested_name = ["fz", "compiler2", "pull", "product", "requested"].map(str::to_string);
    let evaluated_name = ["fz", "compiler2", "pull", "product", "evaluated"].map(str::to_string);
    let settled_name = ["fz", "compiler2", "pull", "product", "settled"].map(str::to_string);
    let normalized_product = |event: &crate::telemetry::causal::PublicEvent| {
        let mut product = event.metadata["product"].clone();
        product
            .as_object_mut()
            .expect("product identity is an object")
            .remove("opaque_type");
        product
    };
    let is_root = |event: &&crate::telemetry::causal::PublicEvent| {
        event.metadata["product"]["kind"] == "root_backend_product"
            && event.metadata["product"]["root_id"] == u64::from(root.as_u32())
    };
    let all_requests = events
        .iter()
        .filter(|event| event.name == requested_name)
        .map(|event| event.metadata["request_id"].as_u64().expect("request identity"))
        .collect::<Vec<_>>();
    let all_evaluations = events
        .iter()
        .filter(|event| event.name == evaluated_name)
        .map(|event| event.metadata["request_id"].as_u64().expect("evaluation identity"))
        .collect::<Vec<_>>();
    assert_eq!(all_requests, (1..=8).collect::<Vec<_>>());
    assert_eq!(all_evaluations, (1..=7).collect::<Vec<_>>());
    let requests = events
        .iter()
        .filter(|event| event.name == requested_name && is_root(event))
        .map(|event| event.metadata["request_id"].as_u64().expect("request identity"))
        .collect::<Vec<_>>();
    let evaluations = events
        .iter()
        .filter(|event| event.name == evaluated_name && is_root(event))
        .map(|event| event.metadata["request_id"].as_u64().expect("evaluation identity"))
        .collect::<Vec<_>>();
    assert_eq!(requests, [2, 4, 7, 8]);
    assert_eq!(evaluations, [2, 4, 7]);

    let (moved_position, moved_event) = events
        .iter()
        .enumerate()
        .find(|(_, event)| event.name == settled_name && event.metadata["product"]["function_id"] == 903)
        .expect("the exact moved dependency settlement");
    let moved_product = normalized_product(moved_event);
    let dependency_product = events
        .iter()
        .find(|event| event.name == requested_name && event.metadata["request_id"] == 1)
        .map(normalized_product)
        .expect("the recursive dependency request");
    let request_position = events
        .iter()
        .position(|event| event.name == requested_name && event.metadata["request_id"] == 4)
        .expect("the moved producer request");

    let report = CausalReport::derive(&events);
    let initial_evaluation = report
        .product_evaluations
        .iter()
        .find(|evaluation| evaluation.request == 2)
        .expect("initial root producer run");
    let moved_evaluation = report
        .product_evaluations
        .iter()
        .find(|evaluation| evaluation.request == 4)
        .expect("producer run after dependency movement");
    assert_eq!(moved_evaluation.prior_evaluation, Some(initial_evaluation.position));
    assert_eq!(moved_evaluation.cause, ProductEvaluationCause::ProductMovement);
    assert_eq!(moved_evaluation.prior_waits.len(), 2);
    assert!(matches!(
        &moved_evaluation.prior_waits[0],
        ProductEvaluationWait::Product(product) if product.raw == moved_product
    ));
    assert!(matches!(
        &moved_evaluation.prior_waits[1],
        ProductEvaluationWait::Product(product) if product.raw == dependency_product
    ));
    assert_eq!(moved_evaluation.triggers.len(), 1);
    let trigger = &moved_evaluation.triggers[0];
    assert_eq!(trigger.position, moved_position);
    assert_eq!(trigger.kind, ProductEvaluationTriggerKind::ProductSettlement);
    assert!(matches!(
        &trigger.dependency,
        ProductEvaluationWait::Product(product) if product.raw == moved_product
    ));
    let search = report
        .recursive_searches
        .iter()
        .find(|search| search.request == Some(4) && search.product == moved_evaluation.product)
        .expect("recursive search inside the moved producer run");
    assert_eq!(search.session, moved_evaluation.session);
    assert_eq!(search.dependency.raw, dependency_product);
    assert_eq!(search.cause, Some(ProductEvaluationCause::ProductMovement));
    assert!(
        initial_evaluation.position < moved_position
            && moved_position < request_position
            && request_position < search.position
            && search.position < moved_evaluation.position
    );
}

#[test]
fn product_driver_refreshes_deepest_stale_child_without_waking_equal_value_readers() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(7);
    let executable = fake_executable(root);
    let parent = ProductKey::RootBackendProduct(root);
    let child = ProductKey::AbiExecutable(executable.clone());
    let fact = FactUse::current(FactKey::CodeIndexed(super::super::SourceOwner::for_test(0)));
    let mut producers = FakeProducers {
        root_entry: Some(executable),
        runtime_fact: Some(fact.clone()),
        facts: HashMap::from([(
            fact.fact().clone(),
            FactState {
                revision: Some(1),
                settled: false,
            },
        )]),
        ..FakeProducers::default()
    };
    let mut driver = ProductDriver::new(&tel, root);

    assert_eq!(
        driver.pull(&mut producers, parent.clone()),
        PullOutcome::wait_on_product(child.clone())
    );
    assert_eq!(
        driver.pull(&mut producers, child.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        driver.pull(&mut producers, parent.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(driver.session().memo().generation(&child), Some(1));
    assert_eq!(driver.session().memo().generation(&parent), Some(1));

    producers.facts.insert(
        fact.fact().clone(),
        FactState {
            revision: Some(2),
            settled: false,
        },
    );
    driver.apply_fact_movements(&[fact_movement(fact.fact().clone(), Some(2), true)]);
    let reads_before_cache_pull = producers.fact_state_reads;
    assert_eq!(
        driver.pull(&mut producers, parent.clone()),
        PullOutcome::wait_on_product(child.clone())
    );
    assert_eq!(producers.fact_state_reads, reads_before_cache_pull);
    assert_eq!(driver.session().memo().generation(&parent), Some(1));
    assert_eq!(driver.session().memo().generation(&child), None);
    assert_eq!(
        driver.pull(&mut producers, child.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(driver.session().memo().generation(&child), Some(1));
    assert_eq!(
        driver.pull(&mut producers, parent.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(driver.session().memo().generation(&parent), Some(1));

    producers.facts.insert(
        fact.fact().clone(),
        FactState {
            revision: Some(3),
            settled: false,
        },
    );
    driver.apply_fact_movements(&[fact_movement(fact.fact().clone(), Some(3), true)]);
    let changed_value = ProductValue::ExecutableEffects(EffectSummary {
        allocates: true,
        ..EffectSummary::default()
    });
    producers.runtime_value = Some(changed_value.clone());
    assert_eq!(
        driver.pull(&mut producers, parent.clone()),
        PullOutcome::wait_on_product(child.clone())
    );
    assert_eq!(
        driver.pull(&mut producers, child.clone()),
        PullOutcome::Produced(changed_value)
    );
    assert_eq!(driver.session().memo().generation(&child), Some(2));
    assert_eq!(driver.session().memo().generation(&parent), None);
    assert_eq!(
        driver.pull(&mut producers, parent.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(driver.session().memo().generation(&parent), Some(1));
    assert_eq!(producers.calls.iter().filter(|called| **called == parent).count(), 3);
}

#[test]
fn readiness_movement_invalidates_a_mixed_current_and_settled_fact_reader() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(70);
    let fact = FactKey::CodeIndexed(super::super::SourceOwner::for_test(0));
    let key = ProductKey::AbiExecutable(fake_executable(root));
    let mut driver = ProductDriver::new(&tel, root);
    finish_test_entry(
        &mut driver.session_mut().memo,
        &tel,
        &key,
        ProductValue::Unit,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::new(),
            facts: HashMap::from([
                (
                    FactUse::current(fact.clone()),
                    FactState {
                        revision: Some(1),
                        settled: false,
                    },
                ),
                (
                    FactUse::settled(fact.clone()),
                    FactState {
                        revision: Some(1),
                        settled: true,
                    },
                ),
            ]),
        },
        &fake_types(),
    );

    driver.apply_fact_movements(&[fact_movement(fact, Some(1), false)]);

    assert!(driver.session().memo().get(&key).is_some());
    let mut producers = FakeProducers::default();
    assert_eq!(
        driver.pull(&mut producers, key.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(producers.calls, vec![key]);
}

#[test]
fn settled_reader_coalesces_dirty_and_equal_resettlement() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(71);
    let fact = FactKey::CodeIndexed(super::super::SourceOwner::for_test(0));
    let key = ProductKey::AbiExecutable(fake_executable(root));
    let mut driver = ProductDriver::new(&tel, root);
    finish_test_entry(
        &mut driver.session_mut().memo,
        &tel,
        &key,
        ProductValue::Unit,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::new(),
            facts: HashMap::from([(
                FactUse::settled(fact.clone()),
                FactState {
                    revision: Some(1),
                    settled: true,
                },
            )]),
        },
        &fake_types(),
    );
    for _ in 0..100 {
        driver.apply_fact_movements(&[fact_movement(fact.clone(), Some(1), false)]);
        driver.apply_fact_movements(&[fact_movement(fact.clone(), Some(1), true)]);
    }
    assert_eq!(driver.session().pending_fact_states.len(), 1);
    assert!(driver.session().memo.fact_stale_dependencies.is_empty());
    assert!(driver.session().memo.dirty_descendants.is_empty());

    let mut producers = FakeProducers::default();
    assert_eq!(
        driver.pull(&mut producers, key),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(producers.calls.is_empty());
}

#[test]
fn settled_reader_reproduces_after_changed_resettlement() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(72);
    let fact = FactKey::CodeIndexed(super::super::SourceOwner::for_test(0));
    let key = ProductKey::AbiExecutable(fake_executable(root));
    let mut driver = ProductDriver::new(&tel, root);
    finish_test_entry(
        &mut driver.session_mut().memo,
        &tel,
        &key,
        ProductValue::Unit,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::new(),
            facts: HashMap::from([(
                FactUse::settled(fact.clone()),
                FactState {
                    revision: Some(1),
                    settled: true,
                },
            )]),
        },
        &fake_types(),
    );
    driver.apply_fact_movements(&[fact_movement(fact, Some(2), true)]);

    let mut producers = FakeProducers::default();
    assert_eq!(
        driver.pull(&mut producers, key.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(producers.calls, vec![key]);
}

#[test]
fn equal_parent_reproduction_does_not_invalidate_its_grandparent() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(17);
    let executable = fake_executable(root);
    let grandparent = ProductKey::RootBackendProduct(root);
    let parent = ProductKey::AbiExecutable(executable.clone());
    let child = ProductKey::BackendExecutable(executable);
    let fact = FactUse::current(FactKey::CodeIndexed(super::super::SourceOwner::for_test(0)));
    let mut producers = FakeProducers {
        root_entry: match &parent {
            ProductKey::AbiExecutable(executable) => Some(executable.clone()),
            _ => unreachable!(),
        },
        runtime_children: HashMap::from([(parent.clone(), child.clone())]),
        backend_fact: Some(fact.clone()),
        facts: HashMap::from([(
            fact.fact().clone(),
            FactState {
                revision: Some(1),
                settled: false,
            },
        )]),
        ..FakeProducers::default()
    };
    let mut driver = ProductDriver::new(&tel, root);

    assert_eq!(
        driver.pull(&mut producers, grandparent.clone()),
        PullOutcome::wait_on_product(parent.clone())
    );
    assert_eq!(
        driver.pull(&mut producers, parent.clone()),
        PullOutcome::wait_on_product(child.clone())
    );
    assert_eq!(
        driver.pull(&mut producers, child.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        driver.pull(&mut producers, parent.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        driver.pull(&mut producers, grandparent.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );

    producers.facts.insert(
        fact.fact().clone(),
        FactState {
            revision: Some(2),
            settled: false,
        },
    );
    let changed_value = ProductValue::ExecutableEffects(EffectSummary {
        allocates: true,
        ..EffectSummary::default()
    });
    producers.backend_value = Some(changed_value.clone());
    driver.apply_fact_movements(&[fact_movement(fact.fact().clone(), Some(2), false)]);
    assert_eq!(
        driver.pull(&mut producers, grandparent.clone()),
        PullOutcome::wait_on_product(child.clone())
    );
    assert_eq!(driver.session().memo().generation(&grandparent), Some(1));
    assert_eq!(driver.session().memo().generation(&parent), Some(1));
    assert_eq!(driver.pull(&mut producers, child), PullOutcome::Produced(changed_value));
    assert_eq!(driver.session().memo().generation(&parent), None);
    assert_eq!(driver.session().memo().generation(&grandparent), Some(1));
    assert_eq!(
        driver.pull(&mut producers, grandparent.clone()),
        PullOutcome::wait_on_product(parent.clone())
    );
    assert_eq!(
        driver.pull(&mut producers, parent.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(driver.session().memo().generation(&parent), Some(1));
    assert_eq!(driver.session().memo().generation(&grandparent), Some(1));
    let grandparent_calls = producers.calls.iter().filter(|called| **called == grandparent).count();
    assert_eq!(
        driver.pull(&mut producers, grandparent.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        producers.calls.iter().filter(|called| **called == grandparent).count(),
        grandparent_calls
    );
    assert_eq!(driver.session().memo().generation(&grandparent), Some(1));
}

#[test]
fn product_driver_reports_fact_waits_as_waits_not_scheduler_work() {
    let tel = ConfiguredTelemetry::new();
    let capture = ProductTelemetryCapture::install(&tel);
    let root = RootId::for_test(1);
    let executable = fake_executable(root);
    let key = ProductKey::BackendExecutable(executable);
    let mut producers = FakeProducers {
        backend_fact: Some(FactUse::current(FactKey::CodeIndexed(
            super::super::SourceOwner::for_test(0),
        ))),
        ..FakeProducers::default()
    };
    let mut driver = ProductDriver::new(&tel, root);

    let outcome = driver.pull(&mut producers, key.clone());

    assert_eq!(
        outcome,
        PullOutcome::wait_on_fact(FactUse::current(FactKey::CodeIndexed(
            super::super::SourceOwner::for_test(0)
        )))
    );
    assert!(driver.session().memo().get(&key).is_none());
    assert!(!driver.session().memo().contains_in_progress(&key));
    assert_eq!(capture.produced.get(), 0);
}

#[test]
fn product_driver_rejects_an_in_progress_key_before_request_telemetry() {
    let tel = ConfiguredTelemetry::new();
    let requests = Rc::new(Cell::new(0));
    let observed = Rc::clone(&requests);
    tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(PRODUCT_REQUESTED_EVENT, move |_, _, _, _, _| {
        observed.set(observed.get() + 1)
    });
    let root = RootId::for_test(2);
    let executable = fake_executable(root);
    let key = ProductKey::ExecutableEffects(executable);
    let mut driver = ProductDriver::new(&tel, root);
    let mut producers = FakeProducers::default();

    assert!(driver.session_mut().memo.begin(key.clone()));
    assert!(catch_unwind(AssertUnwindSafe(|| driver.pull(&mut producers, key.clone()))).is_err());
    assert_eq!(requests.get(), 0);
    assert_eq!(driver.session().request_ids.next, NonZeroU64::new(1));
    assert!(driver.session().memo.contains_in_progress(&key));
    assert!(producers.calls.is_empty());
}

#[test]
fn executable_effects_reads_only_its_local_projection_and_direct_callee_products() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(79);
    let caller = fake_executable_with_function(root, 790);
    let callee = fake_executable_with_function(root, 791);
    let leaf = fake_executable_with_function(root, 792);
    let mut driver = ProductDriver::new(&tel, root);
    record_effect_product(&mut driver.session_mut(), &caller, &[&callee], false);
    record_effect_product(&mut driver.session_mut(), &callee, &[&leaf], false);
    record_effect_product(&mut driver.session_mut(), &leaf, &[], true);
    let mut world = World::new();
    let caller_effects = ProductKey::ExecutableEffects(caller.clone());
    let callee_effects = ProductKey::ExecutableEffects(callee);
    let caller_materialized = ProductKey::MaterializedExecutable(caller);

    let outcome = {
        let mut producers = WorldProductProducers::new(&mut world, &tel);
        driver.pull(&mut producers, caller_effects.clone())
    };

    assert_eq!(outcome, PullOutcome::wait_on_product(callee_effects.clone()));
    let dependencies = driver
        .session()
        .memo()
        .dependency_edges()
        .filter(|(reader, _)| *reader == &caller_effects)
        .map(|(_, dependency)| dependency.clone())
        .collect::<HashSet<_>>();
    assert_eq!(dependencies, HashSet::from([caller_materialized, callee_effects]));
}

#[test]
fn executable_effects_product_settles_symbolic_mutual_recursion_without_root_loop() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(8);
    let first = fake_executable_with_function(root, 80);
    let second = fake_executable_with_function(root, 81);
    let leaf = fake_executable_with_function(root, 82);
    let mut driver = ProductDriver::new(&tel, root);
    record_effect_product(&mut driver.session_mut(), &first, &[&second], false);
    record_effect_product(&mut driver.session_mut(), &second, &[&first, &leaf], false);
    record_effect_product(&mut driver.session_mut(), &leaf, &[], true);
    let mut world = World::new();
    let effects = pull_effects_until_produced(&mut driver, &mut world, &second);
    assert!(effects.allocates, "effects should propagate through mutual recursion");
    assert!(memo_effects(&driver.session(), &first).is_some_and(|effects| effects.allocates));
    assert!(memo_effects(&driver.session(), &second).is_some_and(|effects| effects.allocates));
    for member in [&first, &second] {
        let expected_dependencies = if member == &first {
            HashSet::from([
                ProductKey::MaterializedExecutable(first.clone()),
                ProductKey::ExecutableEffects(second.clone()),
            ])
        } else {
            HashSet::from([
                ProductKey::MaterializedExecutable(second.clone()),
                ProductKey::ExecutableEffects(first.clone()),
                ProductKey::ExecutableEffects(leaf.clone()),
            ])
        };
        let dependencies = driver
            .session()
            .memo()
            .product_dependencies(&ProductKey::ExecutableEffects(member.clone()))
            .expect("every recursive member has a dependency snapshot")
            .keys()
            .cloned()
            .collect::<HashSet<_>>();
        assert_eq!(
            dependencies, expected_dependencies,
            "each member retains exactly its own local and recursive reads"
        );
    }
    assert_eq!(driver.session().producer_pokes(), 0);
}

#[test]
fn executable_effects_selects_the_group_after_all_direct_reads() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(88);
    let anchor = fake_executable_with_function(root, 880);
    let first = fake_executable_with_function(root, 881);
    let second = fake_executable_with_function(root, 882);
    let mut driver = ProductDriver::new(&tel, root);
    record_effect_product(&mut driver.session_mut(), &anchor, &[&first, &second], false);
    record_effect_product(&mut driver.session_mut(), &first, &[&anchor], false);
    record_effect_product(&mut driver.session_mut(), &second, &[&anchor], true);
    let mut world = World::new();
    for member in [&first, &second] {
        let outcome = {
            let mut producers = WorldProductProducers::new(&mut world, &tel);
            driver.pull(&mut producers, ProductKey::ExecutableEffects(member.clone()))
        };
        assert_eq!(
            outcome,
            PullOutcome::wait_on_product(ProductKey::ExecutableEffects(anchor.clone()))
        );
    }

    let effects = pull_effects_until_produced(&mut driver, &mut world, &anchor);

    assert!(effects.allocates);
    for member in [&anchor, &first, &second] {
        let mut expected_dependencies = HashSet::from([ProductKey::MaterializedExecutable(member.clone())]);
        if member == &anchor {
            expected_dependencies.extend([
                ProductKey::ExecutableEffects(first.clone()),
                ProductKey::ExecutableEffects(second.clone()),
            ]);
        } else {
            expected_dependencies.insert(ProductKey::ExecutableEffects(anchor.clone()));
        }
        assert_eq!(
            driver
                .session()
                .memo()
                .product_dependencies(&ProductKey::ExecutableEffects(member.clone()))
                .expect("every member of the complete group must settle")
                .keys()
                .cloned()
                .collect::<HashSet<_>>(),
            expected_dependencies
        );
        assert!(memo_effects(&driver.session(), member).is_some_and(|effects| effects.allocates));
    }
}

#[test]
fn executable_effects_self_cycle_uses_the_generic_recursive_group() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(89);
    let executable = fake_executable_with_function(root, 890);
    let mut driver = ProductDriver::new(&tel, root);
    record_effect_product(&mut driver.session_mut(), &executable, &[&executable], true);
    let mut world = World::new();

    assert_eq!(
        pull_effects_until_produced(&mut driver, &mut world, &executable),
        EffectSummary {
            allocates: true,
            ..EffectSummary::default()
        }
    );
    assert_eq!(
        driver
            .session()
            .memo()
            .product_dependencies(&ProductKey::ExecutableEffects(executable.clone()))
            .expect("self-recursive effects retain their local and recursive reads")
            .keys()
            .cloned()
            .collect::<HashSet<_>>(),
        HashSet::from([
            ProductKey::MaterializedExecutable(executable.clone()),
            ProductKey::ExecutableEffects(executable)
        ])
    );
}

#[test]
fn unchanged_local_effect_reproduces_once_without_waking_its_caller() {
    let tel = ConfiguredTelemetry::new();
    let evaluations = capture_product_evaluations(&tel);
    let root = RootId::for_test(90);
    let caller = fake_executable_with_function(root, 90);
    let callee = fake_executable_with_function(root, 91);
    let mut driver = ProductDriver::new(&tel, root);
    record_effect_product(&mut driver.session_mut(), &caller, &[&callee], false);
    let callee_materialized = fake_effect_materialized(&callee, &[], false);
    record_materialized_product(&mut driver.session_mut(), callee.clone(), callee_materialized.clone());
    let mut world = World::new();
    assert_eq!(
        pull_effects_until_produced(&mut driver, &mut world, &caller),
        EffectSummary::default()
    );
    let callee_generation = driver
        .session()
        .memo()
        .generation(&ProductKey::ExecutableEffects(callee.clone()));
    let caller_generation = driver
        .session()
        .memo()
        .generation(&ProductKey::ExecutableEffects(caller.clone()));
    evaluations.borrow_mut().clear();

    let mut changed_materialized = callee_materialized;
    changed_materialized.original_entry_ids = vec![ControlEntryId::from_u32(17)];
    record_materialized_product(&mut driver.session_mut(), callee.clone(), changed_materialized);

    assert_eq!(
        pull_effects_until_produced(&mut driver, &mut world, &caller),
        EffectSummary::default()
    );
    assert_eq!(
        evaluations.borrow().as_slice(),
        &[ProductKey::ExecutableEffects(callee.clone())],
        "the moved local product must re-evaluate its formula without re-evaluating an unchanged dependent"
    );
    assert_eq!(
        driver
            .session()
            .memo()
            .generation(&ProductKey::ExecutableEffects(callee)),
        callee_generation,
        "equal effect reproduction preserves its generation"
    );
    assert_eq!(
        driver
            .session()
            .memo()
            .generation(&ProductKey::ExecutableEffects(caller)),
        caller_generation
    );
}

#[test]
fn effect_dependencies_follow_edge_add_remove_and_changed_leaf_exactly() {
    let tel = ConfiguredTelemetry::new();
    let evaluations = capture_product_evaluations(&tel);
    let root = RootId::for_test(93);
    let grand = fake_executable_with_function(root, 93);
    let caller = fake_executable_with_function(root, 94);
    let callee = fake_executable_with_function(root, 95);
    let unreachable = fake_executable_with_function(root, 96);
    let mut driver = ProductDriver::new(&tel, root);
    record_effect_product(&mut driver.session_mut(), &grand, &[&caller], false);
    record_effect_product(&mut driver.session_mut(), &caller, &[], false);
    record_effect_product(&mut driver.session_mut(), &callee, &[], false);
    record_effect_product(&mut driver.session_mut(), &unreachable, &[], false);
    let mut world = World::new();
    for executable in [&grand, &callee, &unreachable] {
        assert_eq!(
            pull_effects_until_produced(&mut driver, &mut world, executable),
            EffectSummary::default()
        );
    }

    evaluations.borrow_mut().clear();
    record_effect_product(&mut driver.session_mut(), &caller, &[&callee], false);
    assert_eq!(
        pull_effects_until_produced(&mut driver, &mut world, &grand),
        EffectSummary::default()
    );
    assert_eq!(
        evaluations.borrow().as_slice(),
        &[ProductKey::ExecutableEffects(caller.clone())],
        "adding an effect-free edge re-evaluates its owner, while equal retention keeps its caller quiet"
    );

    evaluations.borrow_mut().clear();
    record_effect_product(&mut driver.session_mut(), &callee, &[], true);
    let allocating = EffectSummary {
        allocates: true,
        ..EffectSummary::default()
    };
    assert_eq!(pull_effects_until_produced(&mut driver, &mut world, &grand), allocating);
    assert_eq!(
        evaluations.borrow().as_slice(),
        &[
            ProductKey::ExecutableEffects(callee.clone()),
            ProductKey::ExecutableEffects(caller.clone()),
            ProductKey::ExecutableEffects(grand.clone()),
        ],
        "a changed leaf re-evaluates only the exact reverse dependents"
    );

    evaluations.borrow_mut().clear();
    record_effect_product(&mut driver.session_mut(), &caller, &[], false);
    assert_eq!(
        pull_effects_until_produced(&mut driver, &mut world, &grand),
        EffectSummary::default()
    );
    assert_eq!(
        evaluations.borrow().as_slice(),
        &[
            ProductKey::ExecutableEffects(caller),
            ProductKey::ExecutableEffects(grand.clone()),
        ],
        "removing the edge re-evaluates its owner and the dependent whose answer changes"
    );

    evaluations.borrow_mut().clear();
    record_effect_product(&mut driver.session_mut(), &callee, &[], false);
    assert_eq!(
        pull_effects_until_produced(&mut driver, &mut world, &callee),
        EffectSummary::default()
    );
    assert_eq!(
        pull_effects_until_produced(&mut driver, &mut world, &grand),
        EffectSummary::default()
    );
    assert_eq!(
        pull_effects_until_produced(&mut driver, &mut world, &unreachable),
        EffectSummary::default()
    );
    assert_eq!(
        evaluations.borrow().as_slice(),
        &[ProductKey::ExecutableEffects(callee)],
        "after edge removal, neither former dependents nor unreachable products re-evaluate"
    );
}

#[test]
fn displaced_effect_dependencies_cannot_close_a_reversed_edge_cycle() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(97);
    let first = fake_executable_with_function(root, 970);
    let second = fake_executable_with_function(root, 971);
    let mut driver = ProductDriver::new(&tel, root);
    record_effect_product(&mut driver.session_mut(), &first, &[], true);
    record_effect_product(&mut driver.session_mut(), &second, &[&first], false);
    let mut world = World::new();
    assert!(pull_effects_until_produced(&mut driver, &mut world, &second).allocates);

    record_effect_product(&mut driver.session_mut(), &first, &[&second], true);
    record_effect_product(&mut driver.session_mut(), &second, &[], false);

    assert!(pull_effects_until_produced(&mut driver, &mut world, &first).allocates);
    assert_eq!(
        memo_effects(&driver.session(), &second),
        Some(EffectSummary::default()),
        "the displaced second formula's retired edge must not make it a member of the reversed dependency"
    );
    assert_eq!(
        driver
            .session()
            .memo()
            .product_dependencies(&ProductKey::ExecutableEffects(second.clone()))
            .expect("the second effects formula must settle independently")
            .keys()
            .cloned()
            .collect::<HashSet<_>>(),
        HashSet::from([ProductKey::MaterializedExecutable(second.clone())])
    );
    assert_eq!(
        driver
            .session()
            .memo()
            .product_dependencies(&ProductKey::ExecutableEffects(first.clone()))
            .expect("the first effects formula must retain its new edge")
            .keys()
            .cloned()
            .collect::<HashSet<_>>(),
        HashSet::from([
            ProductKey::MaterializedExecutable(first),
            ProductKey::ExecutableEffects(second),
        ])
    );
}

#[test]
fn dirty_external_chain_retracts_a_pending_effect_group_snapshot() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(98);
    let leaf = fake_executable_with_function(root, 980);
    let external = fake_executable_with_function(root, 981);
    let anchor = fake_executable_with_function(root, 982);
    let peer = fake_executable_with_function(root, 983);
    let mut driver = ProductDriver::new(&tel, root);
    record_effect_product(&mut driver.session_mut(), &leaf, &[], true);
    record_effect_product(&mut driver.session_mut(), &external, &[&leaf], false);
    record_effect_product(&mut driver.session_mut(), &anchor, &[&peer], false);
    record_effect_product(&mut driver.session_mut(), &peer, &[&external, &anchor], false);
    let mut world = World::new();
    assert!(pull_effects_until_produced(&mut driver, &mut world, &external).allocates);
    let pending = {
        let mut producers = WorldProductProducers::new(&mut world, &tel);
        driver.pull(&mut producers, ProductKey::ExecutableEffects(peer.clone()))
    };
    assert_eq!(
        pending,
        PullOutcome::wait_on_product(ProductKey::ExecutableEffects(anchor.clone()))
    );

    record_effect_product(&mut driver.session_mut(), &leaf, &[], false);

    assert_eq!(
        pull_effects_until_produced(&mut driver, &mut world, &anchor),
        EffectSummary::default(),
        "the group must wait for the dirty external chain instead of publishing its stale effect"
    );
    assert_eq!(
        driver
            .session()
            .memo()
            .generation(&ProductKey::ExecutableEffects(leaf.clone())),
        Some(2)
    );
    assert_eq!(
        driver
            .session()
            .memo()
            .generation(&ProductKey::ExecutableEffects(external.clone())),
        Some(2)
    );
    let session = driver.session();
    let group_dependencies = session
        .memo()
        .product_dependencies(&ProductKey::ExecutableEffects(anchor.clone()))
        .expect("the refreshed group must settle");
    assert_eq!(
        group_dependencies.keys().cloned().collect::<HashSet<_>>(),
        HashSet::from([
            ProductKey::MaterializedExecutable(anchor.clone()),
            ProductKey::ExecutableEffects(peer.clone()),
        ])
    );
    assert_eq!(
        session
            .memo()
            .product_dependencies(&ProductKey::ExecutableEffects(peer))
            .unwrap()
            .get(&ProductKey::ExecutableEffects(external.clone())),
        Some(&Some(2))
    );
    assert_eq!(
        driver
            .session()
            .memo()
            .product_dependencies(&ProductKey::ExecutableEffects(external))
            .expect("the external formula must refresh after its leaf")
            .get(&ProductKey::ExecutableEffects(leaf)),
        Some(&Some(2))
    );
}

#[test]
fn pull_session_lifecycle_finishes_on_drop_and_reports_producer_pokes() {
    let tel = ConfiguredTelemetry::new();
    let observed = Rc::new(Cell::new(None));
    let sink = Rc::clone(&observed);
    tel.attach_raw_event1::<PullSession, _>(
        &["fz", "compiler2", "pull", "session", "finished"],
        move |_, _, _, session| {
            sink.set(Some((
                session.id().expect("emitted sessions have identities"),
                session.demanded_executables.len(),
                session.producer_pokes,
            )));
        },
    );
    let root = RootId::for_test(5);
    let executable = fake_executable(root);
    let mut driver = ProductDriver::new(&tel, root);
    let mut producers = FakeProducers::default();

    assert_eq!(
        driver.pull(&mut producers, ProductKey::AbiExecutable(executable)),
        PullOutcome::Produced(ProductValue::Unit)
    );
    driver.session_mut().record_producer_pokes(2);
    let session_id = driver.session().id().expect("enabled session telemetry");
    drop(driver);

    assert_eq!(observed.get(), Some((session_id, 1, 2)));
    let second = ProductDriver::new(&tel, RootId::for_test(6));
    let second_id = second.session().id().expect("enabled session telemetry");
    drop(second);
    assert_ne!(second_id, session_id);
}

#[test]
fn pull_session_id_exhaustion_never_wraps_or_emits_a_reserved_identity() {
    let counter = AtomicU64::new(u64::MAX - 1);
    assert_eq!(allocate_pull_session_id(&counter).get(), u64::MAX - 1);
    assert_eq!(allocate_pull_session_id(&counter).get(), u64::MAX);
    assert_eq!(counter.load(Ordering::Relaxed), 0);
    assert!(catch_unwind(|| allocate_pull_session_id(&counter)).is_err());
    assert_eq!(counter.load(Ordering::Relaxed), 0, "exhaustion must be permanent");

    let tel = ConfiguredTelemetry::new();
    let starts = Rc::new(Cell::new(0));
    let observed = Rc::clone(&starts);
    tel.attach_raw_event1::<PullSessionId, _>(SESSION_STARTED_EVENT, move |_, _, _, _| {
        observed.set(observed.get() + 1);
    });
    let result = catch_unwind(AssertUnwindSafe(|| {
        ProductDriver::with_session_id_source(&tel, PullSession::new(RootId::for_test(8)), || {
            panic!("pull session identity exhausted")
        })
    }));
    assert!(result.is_err());
    assert_eq!(starts.get(), 0, "identity exhaustion must precede session telemetry");
}

#[test]
fn product_request_id_exhaustion_precedes_telemetry_and_cannot_reuse_zero() {
    let tel = ConfiguredTelemetry::new();
    let requests = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&requests);
    tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(PRODUCT_REQUESTED_EVENT, move |_, _, _, _, request| {
        observed.borrow_mut().push(*request)
    });
    let root = RootId::for_test(9);
    let key = ProductKey::AbiExecutable(fake_executable(root));
    let mut driver = ProductDriver::new(&tel, root);
    driver.session_mut().request_ids.next = NonZeroU64::new(u64::MAX);
    let mut producers = FakeProducers::default();

    assert_eq!(
        driver.pull(&mut producers, key.clone()),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        requests
            .borrow()
            .iter()
            .map(|request| request.get())
            .collect::<Vec<_>>(),
        [u64::MAX]
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| driver.pull(&mut producers, key))).is_err(),
        "the request after the last nonzero identity must fail"
    );
    assert_eq!(
        requests
            .borrow()
            .iter()
            .map(|request| request.get())
            .collect::<Vec<_>>(),
        [u64::MAX],
        "exhaustion must happen before a request event"
    );
    assert!(
        driver.session().request_ids.next.is_none(),
        "exhaustion must be permanent"
    );
}

#[test]
fn disabled_telemetry_does_not_mint_a_session_identity() {
    let driver = ProductDriver::new(&crate::telemetry::sink::NullTelemetry, RootId::for_test(5));
    assert_eq!(driver.session().id(), None);

    let configured = ConfiguredTelemetry::new();
    let driver = ProductDriver::new(&configured, RootId::for_test(5));
    assert_eq!(driver.session().id(), None);
}

fn fake_executable(root: RootId) -> ExecutableKey {
    fake_executable_with_function(root, root.as_u32() + 10)
}

fn fake_executable_with_function(root: RootId, function: u32) -> ExecutableKey {
    let mut types = super::super::Types::new();
    fake_executable_in(&mut types, root, function)
}

fn fake_executable_in(types: &mut super::super::Types, root: RootId, function: u32) -> ExecutableKey {
    let function = super::super::FunctionId::from_coordinate(function);
    let activation = super::super::ActivationKey::from_inputs(root, function, &[], types);
    ExecutableKey {
        activation,
        need: super::super::ExecutableNeed::Value,
    }
}

fn fake_types() -> super::super::Types {
    let mut types = super::super::Types::new();
    let _ = super::super::ActivationKey::from_inputs(
        RootId::for_test(0),
        super::super::FunctionId::from_coordinate(0),
        &[],
        &mut types,
    );
    types
}

fn record_materialized_product(
    session: &mut PullSession,
    executable: ExecutableKey,
    materialized: MaterializedExecutable,
) {
    let tel = ConfiguredTelemetry::new();
    finish_test_entry(
        &mut session.memo,
        &tel,
        &ProductKey::MaterializedExecutable(executable),
        ProductValue::MaterializedExecutable(Rc::new(materialized)),
        ProductDependencies::default(),
        &fake_types(),
    );
}

fn record_effect_product(
    session: &mut PullSession,
    executable: &ExecutableKey,
    callees: &[&ExecutableKey],
    allocates: bool,
) {
    record_materialized_product(
        session,
        executable.clone(),
        fake_effect_materialized(executable, callees, allocates),
    );
}

fn memo_effects(session: &PullSession, executable: &ExecutableKey) -> Option<EffectSummary> {
    match session.memo().get(&ProductKey::ExecutableEffects(executable.clone())) {
        Some(ProductValue::ExecutableEffects(effects)) => Some(*effects),
        _ => None,
    }
}

fn pull_effects_until_produced(
    driver: &mut ProductDriver<'_, ConfiguredTelemetry>,
    world: &mut World,
    executable: &ExecutableKey,
) -> EffectSummary {
    let requested = ProductKey::ExecutableEffects(executable.clone());
    let mut stack = vec![requested.clone()];
    while let Some(key) = stack.pop() {
        let outcome = {
            let mut producers = WorldProductProducers::new(world, driver.telemetry());
            driver.pull(&mut producers, key.clone())
        };
        match outcome {
            PullOutcome::Produced(ProductValue::ExecutableEffects(effects)) if key == requested => {
                return effects;
            }
            PullOutcome::Produced(ProductValue::ExecutableEffects(_)) => {}
            PullOutcome::Produced(other) => panic!("effect pull produced unexpected value {other:?}"),
            PullOutcome::Waiting(waits) => {
                stack.push(key);
                for wait in waits.into_iter().rev() {
                    match wait {
                        PullWait::Product(product) => stack.push(product),
                        PullWait::Fact(fact) => panic!("effect-only fixture unexpectedly waited on {fact:?}"),
                    }
                }
            }
            PullOutcome::Failed => panic!("effect product failed"),
        }
    }
    unreachable!("the requested effects product remains on the work stack until it settles")
}

fn capture_product_evaluations(tel: &ConfiguredTelemetry) -> Rc<RefCell<Vec<ProductKey>>> {
    let evaluations = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&evaluations);
    tel.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
        PRODUCT_EVALUATED_EVENT,
        move |_, _, _, product, _, _| sink.borrow_mut().push(product.clone()),
    );
    evaluations
}

/// Build production-consistent effect inputs: the stored projection and
/// the body from which the effect product derives it always agree.
fn fake_effect_materialized(
    executable: &ExecutableKey,
    callees: &[&ExecutableKey],
    allocates: bool,
) -> MaterializedExecutable {
    let executable = executable_symbol_for_test(executable);
    let effects = EffectSummary {
        allocates,
        ..EffectSummary::default()
    };
    let projections = if allocates {
        vec![LoweredStep::Tuple {
            value: ValueId::from_u32(0),
            items: Vec::new(),
        }]
    } else {
        Vec::new()
    };
    let return_position = TransportPosition::ExecutableReturn {
        executable: executable.clone(),
    };
    MaterializedExecutable {
        entry_dispatch: None,
        return_ty: effect_test_ty(),
        runtime_demand: Rc::new(ExecutableRuntimeDemand::default()),
        transport: MaterializedExecutableTransport {
            executable: executable.clone(),
            position_layouts: Vec::new(),
            input_positions: Vec::new(),
            return_position,
            resume_positions: Vec::new(),
            return_payload_positions: Vec::new(),
            entry_capture_positions: Vec::new(),
            call_arg_positions: Vec::new(),
            value_positions: Vec::new(),
        },
        original_entry_ids: Vec::new(),
        value_types: HashMap::new(),
        effects,
        struct_modules: Box::default(),
        body: super::super::LoweredBody::clauses(
            vec![LoweredClause {
                span: crate::source::Span::DUMMY,
                params: Vec::new(),
                projections,
                entry: ControlEntryId::from_u32(0),
            }],
            vec![LoweredEntry {
                span: crate::source::Span::DUMMY,
                origin: ControlEntryOrigin::Clause,
                params: Vec::new(),
                captures: Vec::new(),
                physical_captures: Vec::new(),
                physical_params: Vec::new(),
                steps: Vec::new(),
                tail: LoweredTail::Halt {
                    atom: "done".to_string(),
                },
            }],
            Vec::new(),
        ),
        call_edges: callees
            .iter()
            .enumerate()
            .map(|(index, callee)| {
                (
                    CallSiteId::from_u32(index as u32),
                    fake_effect_edge(
                        (*callee).clone(),
                        executable.clone(),
                        executable_symbol_for_test(callee),
                    ),
                )
            })
            .collect(),
    }
}

fn fake_effect_edge(
    callee: ExecutableKey,
    caller_symbol: ExecutableSymbol,
    callee_symbol: ExecutableSymbol,
) -> MaterializedCallEdge {
    MaterializedCallEdge::Named {
        target: CallEdge::Direct(DirectCallEdge {
            callee: CallTarget::Local(callee),
            return_flow: CallReturnFlow::Tail {
                source: TransportPosition::ExecutableReturn {
                    executable: callee_symbol,
                },
                payload: TransportPosition::ReturnPayload {
                    executable: caller_symbol.clone(),
                    callsite: CallSiteId::from_u32(0),
                },
                caller_return: TransportPosition::ExecutableReturn {
                    executable: caller_symbol,
                },
            },
            extern_marshals: None,
        }),
        return_ty: effect_test_ty(),
    }
}

fn effect_test_ty() -> super::super::Ty {
    let mut types = super::super::Types::new();
    types.none()
}

fn executable_symbol_for_test(executable: &ExecutableKey) -> super::super::transport::ExecutableSymbol {
    super::super::transport::ExecutableSymbol {
        activation: super::super::transport::ActivationSymbol {
            function: executable.activation.function,
            arrow: executable.activation.arrow,
            input: Box::default(),
        },
        need: executable.need,
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
struct OwnerCallableAggregation {
    resolutions: HashSet<ExecutableSymbol>,
    direct_surfaces: HashSet<Box<[ShapeId]>>,
    direct_edges: HashSet<super::super::transport::CallableDirectEdge>,
    boundary_ids: HashSet<BoundaryId>,
}

#[derive(Debug, Default, PartialEq, Eq)]
struct OwnerBoundaryAggregation {
    publications: HashSet<TransportPosition>,
    resolutions: HashSet<ExecutableSymbol>,
}

#[derive(Debug, Default, PartialEq, Eq)]
struct OwnerAggregation {
    callables: HashMap<CallableId, OwnerCallableAggregation>,
    boundaries: HashMap<BoundaryId, OwnerBoundaryAggregation>,
}

fn aggregate_callable_owners(memo: &ProductMemo, owners: &[ProductKey]) -> OwnerAggregation {
    let mut out = OwnerAggregation::default();
    for owner in owners {
        let Some(ProductValue::CallableConstruction(answer)) = memo.get(owner) else {
            continue;
        };
        for (callable, facts) in &answer.callable_facts {
            let aggregate = out.callables.entry(*callable).or_default();
            aggregate.resolutions.extend(facts.resolutions.iter().cloned());
            aggregate.direct_surfaces.extend(facts.direct_surfaces.iter().cloned());
            aggregate.direct_edges.extend(facts.direct_edges.iter().cloned());
            aggregate.boundary_ids.extend(facts.boundary_ids.iter().copied());
        }
        for (boundary, facts) in &answer.boundary_facts {
            let aggregate = out.boundaries.entry(*boundary).or_default();
            aggregate.publications.extend(facts.publications.iter().cloned());
            aggregate.resolutions.extend(facts.resolutions.iter().cloned());
        }
    }
    out
}

fn callable_owner_answer(
    layout: TransportLayout,
    owner: TransportPosition,
    callable: CallableId,
    boundary: BoundaryId,
    resolution: ExecutableSymbol,
) -> ProductValue {
    ProductValue::CallableConstruction(Rc::new(CallableConstructionOwner {
        layout,
        construction: None,
        callable_facts: HashMap::from([(
            callable,
            CallableFacts {
                resolutions: Box::new([resolution.clone()]),
                direct_surfaces: Box::default(),
                direct_edges: Box::default(),
                boundary_ids: Box::new([boundary]),
            },
        )]),
        boundary_facts: HashMap::from([(
            boundary,
            BoundaryFacts {
                publications: Box::new([owner]),
                resolutions: Box::new([resolution]),
            },
        )]),
    }))
}

fn withdrawn_callable_owner_answer(layout: TransportLayout) -> ProductValue {
    ProductValue::CallableConstruction(Rc::new(CallableConstructionOwner {
        layout,
        construction: None,
        callable_facts: HashMap::new(),
        boundary_facts: HashMap::new(),
    }))
}

fn finish_test_product(
    memo: &mut ProductMemo,
    key: &ProductKey,
    value: ProductValue,
    dependencies: impl IntoIterator<Item = ProductKey>,
) {
    let tel = ConfiguredTelemetry::new();
    assert!(memo.begin(key.clone()));
    let products = dependencies
        .into_iter()
        .map(|dependency| {
            let generation = memo.generation(&dependency);
            (dependency, generation)
        })
        .collect();
    assert!(finish_test_entry(
        memo,
        &tel,
        key,
        value,
        ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products,
            facts: HashMap::new(),
        },
        &fake_types(),
    ));
}

#[test]
fn callable_owner_products_aggregate_order_free_and_retract_independently() {
    let types = fake_types();
    let root = RootId::for_test(35);
    let left_position = TransportPosition::Value {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 350)),
        value: ValueId::from_u32(0),
    };
    let right_position = TransportPosition::Value {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 351)),
        value: ValueId::from_u32(0),
    };
    let left_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 352));
    let right_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 353));
    let replacement_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 354));
    let mut world = World::new();
    let callable = world.intern_callable(super::super::transport::CallableDescr {
        function: Some(FunctionId::from_coordinate(355)),
        arity: 0,
        capture_layouts: Box::default(),
    });
    let boundary = BoundaryId::for_test(8);
    let layout = TransportLayout::structural(ShapeId::for_test(9));
    let left_key = ProductKey::CallableConstruction(left_position.clone());
    let right_key = ProductKey::CallableConstruction(right_position.clone());
    let left_abi = ProductKey::AbiExecutable(fake_executable_with_function(root, 350));
    let right_abi = ProductKey::AbiExecutable(fake_executable_with_function(root, 351));
    let root_key = ProductKey::RootBackendProduct(root);
    let mut memo = ProductMemo::default();
    let tel = ConfiguredTelemetry::new();

    let left_value = callable_owner_answer(
        layout,
        left_position.clone(),
        callable,
        boundary,
        left_resolution.clone(),
    );
    let right_value = callable_owner_answer(
        layout,
        right_position.clone(),
        callable,
        boundary,
        right_resolution.clone(),
    );
    finish_test_product(&mut memo, &left_key, left_value, []);
    finish_test_product(&mut memo, &right_key, right_value, []);
    finish_test_product(&mut memo, &left_abi, ProductValue::Unit, [left_key.clone()]);
    finish_test_product(&mut memo, &right_abi, ProductValue::Unit, [right_key.clone()]);
    finish_test_product(
        &mut memo,
        &root_key,
        ProductValue::RootBackendProduct(Rc::new(super::super::artifact::BackendProgram::empty_for_test())),
        [left_abi.clone(), right_abi.clone()],
    );

    let forward = aggregate_callable_owners(&memo, &[left_key.clone(), right_key.clone()]);
    let reverse = aggregate_callable_owners(&memo, &[right_key.clone(), left_key.clone()]);
    assert_eq!(forward, reverse);
    assert_eq!(
        forward.callables[&callable].resolutions,
        HashSet::from([left_resolution.clone(), right_resolution.clone()])
    );
    assert_eq!(
        forward.boundaries[&boundary].publications,
        HashSet::from([left_position.clone(), right_position.clone()])
    );
    assert_eq!(
        memo.product_dependencies(&left_abi).unwrap(),
        &IndexMap::from([(left_key.clone(), Some(1))])
    );
    assert_eq!(
        memo.product_dependencies(&right_abi).unwrap(),
        &IndexMap::from([(right_key.clone(), Some(1))])
    );
    assert_eq!(
        memo.product_dependencies(&root_key).unwrap(),
        &IndexMap::from([(left_abi.clone(), Some(1)), (right_abi.clone(), Some(1))])
    );

    let right_generation = memo.generation(&right_key);
    memo.remove(&tel, &left_key, &types);
    finish_test_product(
        &mut memo,
        &left_key,
        callable_owner_answer(
            layout,
            left_position,
            callable,
            boundary,
            replacement_resolution.clone(),
        ),
        [],
    );
    let replaced_generation = memo.generation(&left_key);
    let replaced = aggregate_callable_owners(&memo, &[left_key.clone(), right_key.clone()]);
    assert_eq!(
        replaced.callables[&callable].resolutions,
        HashSet::from([replacement_resolution, right_resolution.clone()])
    );
    assert!(!replaced.callables[&callable].resolutions.contains(&left_resolution));
    assert_eq!(memo.generation(&right_key), right_generation);
    assert!(memo.stale_dependency(&tel, &left_abi, &types).is_some());
    assert!(memo.stale_dependency(&tel, &right_abi, &types).is_none());
    assert!(memo.stale_dependency(&tel, &root_key, &types).is_some());

    let reproduced = memo.get(&left_key).cloned().expect("replaced owner product");
    memo.remove(&tel, &left_key, &types);
    finish_test_product(&mut memo, &left_key, reproduced, []);
    assert_eq!(memo.generation(&left_key), replaced_generation);
    assert_eq!(memo.generation(&right_key), right_generation);

    memo.remove(&tel, &left_key, &types);
    finish_test_product(&mut memo, &left_key, withdrawn_callable_owner_answer(layout), []);
    let withdrawn = aggregate_callable_owners(&memo, &[left_key, right_key]);
    assert_eq!(
        withdrawn.callables[&callable].resolutions,
        HashSet::from([right_resolution])
    );
    assert_eq!(
        withdrawn.boundaries[&boundary].publications,
        HashSet::from([right_position])
    );
}

type OwnerSymbolKey = (u32, super::super::types::Ty, Vec<super::super::types::Ty>, u8, usize);
type OwnerPositionKey = (u8, OwnerSymbolKey, u64, u64, usize);

fn owner_symbol_key(symbol: &ExecutableSymbol) -> OwnerSymbolKey {
    let need = match symbol.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        symbol.activation.function.as_u32(),
        symbol.activation.arrow,
        symbol.activation.input.to_vec(),
        need.0,
        need.1,
    )
}

fn owner_position_key(position: &TransportPosition) -> OwnerPositionKey {
    let local = match position {
        TransportPosition::ExecutableInput { semantic_index, .. } => (0, 0, 0, *semantic_index),
        TransportPosition::ExecutableReturn { .. } => (1, 0, 0, 0),
        TransportPosition::ResumePayload { callsite, entry, .. } => (
            2,
            callsite.map_or(0, |callsite| u64::from(callsite.as_u32()) + 1),
            u64::from(entry.as_u32()),
            0,
        ),
        TransportPosition::ReturnPayload { callsite, .. } => (3, u64::from(callsite.as_u32()), 0, 0),
        TransportPosition::CallArg {
            callsite,
            semantic_index,
            ..
        } => (4, u64::from(callsite.as_u32()), 0, *semantic_index),
        TransportPosition::EntryCapture {
            entry, capture_index, ..
        } => (5, u64::from(entry.as_u32()), 0, *capture_index),
        TransportPosition::Value { value, .. } => (6, u64::from(value.as_u32()), 0, 0),
    };
    (
        local.0,
        owner_symbol_key(position.executable()),
        local.1,
        local.2,
        local.3,
    )
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OwnerState {
    layout: TransportLayout,
    resolutions: HashSet<ExecutableSymbol>,
    publications: HashSet<TransportPosition>,
}

impl OwnerState {
    fn bottom(layout: TransportLayout) -> Self {
        Self {
            layout,
            resolutions: HashSet::new(),
            publications: HashSet::new(),
        }
    }

    fn join_assign(&mut self, other: &Self) {
        self.resolutions.extend(other.resolutions.iter().cloned());
        self.publications.extend(other.publications.iter().cloned());
    }

    fn product_value(&self, callable: CallableId, boundary: BoundaryId) -> ProductValue {
        let mut resolutions = self.resolutions.iter().cloned().collect::<Vec<_>>();
        resolutions.sort_by_key(owner_symbol_key);
        let direct_edges = resolutions
            .iter()
            .cloned()
            .map(|resolution| super::super::transport::CallableDirectEdge {
                surface_inputs: Box::default(),
                surface_arg_shapes: Box::new([self.layout.structural]),
                resolution,
                capture_semantic_inputs: Box::default(),
                surface_semantic_inputs: Box::default(),
            })
            .collect();
        let mut publications = self.publications.iter().cloned().collect::<Vec<_>>();
        publications.sort_by_key(owner_position_key);
        ProductValue::CallableConstruction(Rc::new(CallableConstructionOwner {
            layout: self.layout,
            construction: None,
            callable_facts: (!resolutions.is_empty())
                .then(|| {
                    (
                        callable,
                        CallableFacts {
                            resolutions: resolutions.clone().into_boxed_slice(),
                            direct_surfaces: Box::new([Box::new([self.layout.structural])]),
                            direct_edges,
                            boundary_ids: Box::new([boundary]),
                        },
                    )
                })
                .into_iter()
                .collect(),
            boundary_facts: (!publications.is_empty() || !resolutions.is_empty())
                .then(|| {
                    (
                        boundary,
                        BoundaryFacts {
                            publications: publications.into_boxed_slice(),
                            resolutions: resolutions.into_boxed_slice(),
                        },
                    )
                })
                .into_iter()
                .collect(),
        }))
    }
}

#[derive(Clone)]
struct OwnerEquation {
    seed: OwnerState,
    children: Vec<usize>,
}

fn settle_owner_equations(equations: &[OwnerEquation], reverse: bool) -> (Vec<OwnerState>, usize) {
    let mut answers = equations
        .iter()
        .map(|equation| OwnerState::bottom(equation.seed.layout))
        .collect::<Vec<_>>();
    let mut order = (0..equations.len()).collect::<Vec<_>>();
    if reverse {
        order.reverse();
    }
    for round in 0..16 {
        let previous = answers.clone();
        for index in order.iter().copied() {
            let mut answer = equations[index].seed.clone();
            for child in &equations[index].children {
                answer.join_assign(&answers[*child]);
            }
            answers[index] = answer;
        }
        if answers == previous {
            return (answers, round);
        }
    }
    panic!("finite callable owner equations did not settle")
}

fn finish_owner_group(
    memo: &mut ProductMemo,
    keys: &[ProductKey],
    answers: &[OwnerState],
    external: &[ProductKey],
    callable: CallableId,
    boundary: BoundaryId,
    reverse: bool,
) {
    let tel = ConfiguredTelemetry::new();
    for key in keys {
        assert!(memo.begin(key.clone()));
        assert!(memo.get(key).is_none());
    }
    let mut order = (0..keys.len()).collect::<Vec<_>>();
    if reverse {
        order.reverse();
    }
    let entries = order
        .into_iter()
        .map(|index| {
            let products = keys
                .iter()
                .chain(external)
                .cloned()
                .map(|dependency| {
                    let generation = memo.generation(&dependency);
                    (dependency, generation)
                })
                .collect();
            (
                keys[index].clone(),
                answers[index].product_value(callable, boundary),
                ProductDependencies {
                    rooted_read: None,
                    membership: HashSet::new(),
                    products,
                    facts: HashMap::new(),
                },
            )
        })
        .collect();
    assert!(finish_test_group(
        memo,
        &tel,
        keys.first().expect("owner group is non-empty"),
        entries,
        &fake_types(),
    ));
}

#[test]
fn transport_shape_group_retains_external_dependencies_on_their_owning_member() {
    let types = fake_types();
    let root = RootId::for_test(38);
    let symbol = executable_symbol_for_test(&fake_executable_with_function(root, 380));
    let left = ProductKey::TransportShape(TransportPosition::Value {
        executable: symbol.clone(),
        value: ValueId::from_u32(1),
    });
    let right = ProductKey::TransportShape(TransportPosition::Value {
        executable: symbol,
        value: ValueId::from_u32(2),
    });
    let external = ProductKey::TransportShape(TransportPosition::ExecutableReturn {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 381)),
    });
    let left_reader = ProductKey::AbiExecutable(fake_executable_with_function(root, 382));
    let right_reader = ProductKey::AbiExecutable(fake_executable_with_function(root, 383));
    let unrelated = ProductKey::AbiExecutable(fake_executable_with_function(root, 384));
    let first_layout = TransportLayout::structural(ShapeId::for_test(110));
    let second_layout = TransportLayout::structural(ShapeId::for_test(111));
    let external_value = |shape| {
        ProductValue::TransportShape(TransportShapeFact::Layout(TransportLayout::structural(
            ShapeId::for_test(shape),
        )))
    };

    for reverse in [false, true] {
        let mut memo = ProductMemo::default();
        let tel = ConfiguredTelemetry::new();
        finish_test_product(&mut memo, &external, external_value(385), []);
        for key in [&left, &right] {
            assert!(memo.begin(key.clone()));
        }
        let mut entries = vec![
            (
                left.clone(),
                ProductValue::TransportShape(TransportShapeFact::Layout(first_layout)),
                ProductDependencies {
                    rooted_read: None,
                    membership: HashSet::new(),
                    products: IndexMap::from([(right.clone(), None), (external.clone(), memo.generation(&external))]),
                    facts: HashMap::new(),
                },
            ),
            (
                right.clone(),
                ProductValue::TransportShape(TransportShapeFact::Layout(first_layout)),
                ProductDependencies {
                    rooted_read: None,
                    membership: HashSet::new(),
                    products: IndexMap::from([(left.clone(), None)]),
                    facts: HashMap::new(),
                },
            ),
        ];
        if reverse {
            entries.reverse();
        }
        assert!(finish_test_group(&mut memo, &tel, &left, entries, &types));
        assert_eq!(
            memo.product_dependencies(&left),
            Some(&IndexMap::from([(right.clone(), Some(1)), (external.clone(), Some(1))]))
        );
        assert_eq!(
            memo.product_dependencies(&right),
            Some(&IndexMap::from([(left.clone(), Some(1))]))
        );

        finish_test_product(&mut memo, &left_reader, ProductValue::Unit, [left.clone()]);
        finish_test_product(&mut memo, &right_reader, ProductValue::Unit, [right.clone()]);
        finish_test_product(&mut memo, &unrelated, ProductValue::Unit, []);
        let unrelated_generation = memo.generation(&unrelated);

        memo.remove(&tel, &external, &types);
        finish_test_product(&mut memo, &external, external_value(386), []);
        assert!(memo.get(&left).is_none());
        assert!(memo.get(&right).is_some());
        assert!(
            memo.has_unsettled_inputs(&right),
            "the indirect reader remains retained until its dependency reproduces"
        );
        assert!(memo.get(&unrelated).is_some());

        for key in [&left, &right] {
            assert!(memo.begin(key.clone()));
        }
        let left_generation = memo.generation(&left);
        let right_generation = memo.generation(&right);
        let external_generation = memo.generation(&external);
        assert!(finish_test_group(
            &mut memo,
            &tel,
            &left,
            vec![
                (
                    left.clone(),
                    ProductValue::TransportShape(TransportShapeFact::Layout(second_layout)),
                    ProductDependencies {
                        rooted_read: None,
                        membership: HashSet::new(),
                        products: IndexMap::from([
                            (right.clone(), right_generation),
                            (external.clone(), external_generation),
                        ]),
                        facts: HashMap::new(),
                    },
                ),
                (
                    right.clone(),
                    ProductValue::TransportShape(TransportShapeFact::Layout(second_layout)),
                    ProductDependencies {
                        rooted_read: None,
                        membership: HashSet::new(),
                        products: IndexMap::from([(left.clone(), left_generation)]),
                        facts: HashMap::new(),
                    },
                ),
            ],
            &types,
        ));
        assert_eq!(memo.generation(&left), Some(2));
        assert_eq!(memo.generation(&right), Some(2));
        assert!(memo.get(&left_reader).is_none());
        assert!(memo.get(&right_reader).is_none());
        assert_eq!(memo.generation(&unrelated), unrelated_generation);
    }
}

/// fz-kdt.34.4 TDD 4: a group settle must emit one `pull.product.settled`
/// event PER MEMBER (not just the anchor `finish_completion` was called for),
/// each carrying its own generation and changed flag, all sharing one
/// `group` id -- and a second, independent group settle must get a
/// DIFFERENT group id. Red before fz-kdt.34.4: only the driver's single
/// anchor-keyed event existed, and it carried no generation/changed/group
/// at all.
#[test]
fn group_settle_emits_one_settled_event_per_member_with_shared_generation_and_group() {
    let tel = ConfiguredTelemetry::new();
    let events: Rc<RefCell<Vec<(ProductKey, ProductValue, ProductSettlement)>>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&events);
    tel.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
        &["fz", "compiler2", "pull", "product", "settled"],
        move |_, _, _, key, value, settlement| {
            sink.borrow_mut().push((key.clone(), value.clone(), *settlement));
        },
    );

    let root = RootId::for_test(60);
    let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 600));
    let right = ProductKey::AbiExecutable(fake_executable_with_function(root, 601));
    let mut memo = ProductMemo::default();

    let first_value = ProductValue::ExecutableEffects(EffectSummary::default());
    let second_value = ProductValue::ExecutableEffects(EffectSummary {
        allocates: true,
        ..EffectSummary::default()
    });

    for key in [&left, &right] {
        assert!(memo.begin(key.clone()));
    }
    assert!(finish_test_group(
        &mut memo,
        &tel,
        &left,
        vec![
            (left.clone(), first_value.clone(), ProductDependencies::default()),
            (right.clone(), first_value.clone(), ProductDependencies::default()),
        ],
        &fake_types(),
    ));

    let first_group_events = events.borrow().clone();
    assert_eq!(
        first_group_events.len(),
        2,
        "a group settle must emit one settled event per member, not just the anchor"
    );
    let first_group_id = first_group_events[0]
        .2
        .group
        .expect("group settlement carries a group id");
    for (key, value, settlement) in &first_group_events {
        assert!(*key == left || *key == right);
        assert_eq!(*value, first_value);
        assert_eq!(settlement.generation, 1, "a first-time settle starts at generation 1");
        assert!(settlement.changed, "a first-time settle is always a change");
        assert_eq!(settlement.group, Some(first_group_id));
    }

    events.borrow_mut().clear();

    for key in [&left, &right] {
        assert!(memo.begin(key.clone()));
    }
    assert!(finish_test_group(
        &mut memo,
        &tel,
        &left,
        vec![
            (left.clone(), first_value, ProductDependencies::default()),
            (right.clone(), second_value, ProductDependencies::default()),
        ],
        &fake_types(),
    ));

    let second_group_events = events.borrow().clone();
    assert_eq!(second_group_events.len(), 2);
    let second_group_id = second_group_events[0]
        .2
        .group
        .expect("group settlement carries a group id");
    assert_ne!(
        second_group_id, first_group_id,
        "a second, independent group settle must get a distinct group id"
    );
    let left_settlement = &second_group_events
        .iter()
        .find(|(key, _, _)| *key == left)
        .expect("left member should have settled")
        .2;
    let right_settlement = &second_group_events
        .iter()
        .find(|(key, _, _)| *key == right)
        .expect("right member should have settled")
        .2;
    assert_eq!(
        left_settlement.generation, 1,
        "a reproduced-unchanged member keeps its prior generation"
    );
    assert!(
        !left_settlement.changed,
        "a reproduced-unchanged member's changed flag is false"
    );
    assert_eq!(right_settlement.generation, 2, "a changed member's generation advances");
    assert!(right_settlement.changed, "a changed member's changed flag is true");
    assert_eq!(left_settlement.group, Some(second_group_id));
    assert_eq!(right_settlement.group, Some(second_group_id));
}

#[test]
fn publication_moves_observation_and_membership_storage_into_the_entry() {
    let tel = ConfiguredTelemetry::new();
    let types = fake_types();
    let root = RootId::for_test(61);
    let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 610));
    let mut executable = executable_symbol_for_test(&fake_executable_with_function(root, 612));
    executable.activation.input = vec![executable.activation.arrow; 32].into_boxed_slice();
    let external = ProductKey::TransportShape(TransportPosition::ExecutableReturn { executable });
    let dependencies = ProductDependencies {
        rooted_read: None,
        membership: HashSet::from([external.clone()]),
        products: IndexMap::from([(external.clone(), Some(7))]),
        facts: HashMap::new(),
    };
    let mut memo = ProductMemo::default();
    let product_storage = dependencies.products.get_index(0).unwrap().0 as *const ProductKey;
    let ProductKey::TransportShape(position) = dependencies.products.get_index(0).unwrap().0 else {
        unreachable!()
    };
    let input_storage = position.executable().activation.input.as_ptr();
    let membership_storage = dependencies.membership.get(&external).unwrap() as *const ProductKey;
    assert!(memo.begin(left.clone()));
    assert!(finish_test_entry(
        &mut memo,
        &tel,
        &left,
        ProductValue::Unit,
        dependencies,
        &types,
    ));
    let entry = &memo.produced[&left];
    assert_eq!(
        entry.dependencies.products.get_index(0).unwrap().0 as *const ProductKey,
        product_storage
    );
    let ProductKey::TransportShape(position) = entry.dependencies.products.get_index(0).unwrap().0 else {
        unreachable!()
    };
    assert_eq!(position.executable().activation.input.as_ptr(), input_storage);
    assert_eq!(
        entry.membership.get(&external).unwrap() as *const ProductKey,
        membership_storage
    );
}

#[test]
fn changed_product_authority_discards_pending_reader_snapshots_before_group_settlement() {
    let types = fake_types();
    let root = RootId::for_test(39);
    let external = ProductKey::AbiExecutable(fake_executable_with_function(root, 390));
    let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 391));
    let right = ProductKey::AbiExecutable(fake_executable_with_function(root, 392));
    let unrelated = ProductKey::AbiExecutable(fake_executable_with_function(root, 393));
    let first = ProductValue::ExecutableEffects(EffectSummary::default());
    let second = ProductValue::ExecutableEffects(EffectSummary {
        allocates: true,
        ..EffectSummary::default()
    });

    for reverse in [false, true] {
        let mut memo = ProductMemo::default();
        let tel = ConfiguredTelemetry::new();
        finish_test_product(&mut memo, &external, first.clone(), []);
        finish_test_product(&mut memo, &unrelated, ProductValue::Unit, []);
        let unrelated_generation = memo.generation(&unrelated);

        assert!(memo.begin(left.clone()));
        memo.unblock(
            ProductRequestId(NonZeroU64::MIN),
            &left,
            ProductDependencies {
                rooted_read: None,
                membership: HashSet::new(),
                products: IndexMap::from([(right.clone(), None), (external.clone(), Some(1))]),
                facts: HashMap::new(),
            },
        );
        assert!(memo.pending_dependencies.contains_key(&left));

        memo.remove(&tel, &external, &types);
        finish_test_product(&mut memo, &external, second.clone(), []);

        assert!(!memo.pending_dependencies.contains_key(&left));
        assert!(
            memo.product_readers
                .get(&external)
                .is_none_or(|readers| !readers.contains(&left))
        );
        assert!(
            memo.product_readers
                .get(&right)
                .is_none_or(|readers| !readers.contains(&left))
        );

        for key in [&left, &right] {
            assert!(memo.begin(key.clone()));
        }
        let mut entries = vec![
            (
                left.clone(),
                ProductValue::Unit,
                ProductDependencies {
                    rooted_read: None,
                    membership: HashSet::new(),
                    products: IndexMap::from([(right.clone(), None), (external.clone(), Some(2))]),
                    facts: HashMap::new(),
                },
            ),
            (
                right.clone(),
                ProductValue::Unit,
                ProductDependencies {
                    rooted_read: None,
                    membership: HashSet::new(),
                    products: IndexMap::from([(left.clone(), None), (external.clone(), Some(2))]),
                    facts: HashMap::new(),
                },
            ),
        ];
        if reverse {
            entries.reverse();
        }
        assert!(finish_test_group(&mut memo, &tel, &left, entries, &types));
        for key in [&left, &right] {
            let peer = if key == &left { &right } else { &left };
            assert_eq!(
                memo.product_dependencies(key),
                Some(&IndexMap::from([(peer.clone(), Some(1)), (external.clone(), Some(2))]))
            );
        }
        assert_eq!(memo.generation(&unrelated), unrelated_generation);
    }
}

#[test]
fn changed_fact_authority_discards_only_pending_readers_of_that_fact() {
    let types = fake_types();
    let root = RootId::for_test(40);
    let reader = ProductKey::AbiExecutable(fake_executable_with_function(root, 400));
    let unrelated = ProductKey::AbiExecutable(fake_executable_with_function(root, 401));
    let fact = FactUse::current(FactKey::CodeIndexed(super::super::SourceOwner::for_test(0)));
    let other_fact = FactUse::settled(FactKey::RootEntry(root));
    let first = FactState {
        revision: Some(1),
        settled: false,
    };
    let second = FactState {
        revision: Some(2),
        settled: false,
    };

    let mut memo = ProductMemo::default();
    let tel = ConfiguredTelemetry::new();
    for (key, dependency, state) in [
        (&reader, fact.clone(), first),
        (
            &unrelated,
            other_fact.clone(),
            FactState {
                revision: Some(1),
                settled: true,
            },
        ),
    ] {
        assert!(memo.begin(key.clone()));
        memo.unblock(
            ProductRequestId(NonZeroU64::MIN),
            key,
            ProductDependencies {
                rooted_read: None,
                membership: HashSet::new(),
                products: IndexMap::new(),
                facts: HashMap::from([(dependency, state)]),
            },
        );
    }

    memo.reconcile_fact_movements(&tel, &HashMap::from([(fact.fact().clone(), first)]), &types);
    assert!(memo.pending_dependencies.contains_key(&reader));
    memo.reconcile_fact_movements(&tel, &HashMap::from([(fact.fact().clone(), second)]), &types);

    assert!(!memo.pending_dependencies.contains_key(&reader));
    assert!(memo.pending_dependencies.contains_key(&unrelated));
    assert!(
        memo.fact_readers
            .get(fact.fact())
            .is_none_or(|readers| !readers.contains(&reader))
    );
    assert!(
        memo.fact_readers
            .get(other_fact.fact())
            .is_some_and(|readers| readers.contains(&unrelated))
    );
}

#[test]
fn group_settlement_rejects_discordant_dependency_snapshots_before_publication() {
    let root = RootId::for_test(41);
    let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 410));
    let right = ProductKey::AbiExecutable(fake_executable_with_function(root, 411));
    let external = ProductKey::AbiExecutable(fake_executable_with_function(root, 412));
    let unrelated = ProductKey::AbiExecutable(fake_executable_with_function(root, 413));
    let fact = FactUse::current(FactKey::CodeIndexed(super::super::SourceOwner::for_test(0)));
    let fact_one = FactState {
        revision: Some(1),
        settled: false,
    };
    let fact_two = FactState {
        revision: Some(2),
        settled: false,
    };

    for reverse in [false, true] {
        for discordant_fact in [false, true] {
            let mut memo = ProductMemo::default();
            let tel = ConfiguredTelemetry::new();
            finish_test_product(&mut memo, &unrelated, ProductValue::Unit, []);
            let unrelated_generation = memo.generation(&unrelated);
            let left_dependencies = ProductDependencies {
                rooted_read: None,
                membership: HashSet::new(),
                products: IndexMap::from([(external.clone(), if discordant_fact { Some(2) } else { Some(1) })]),
                facts: HashMap::from([(fact.clone(), fact_one)]),
            };
            let right_dependencies = ProductDependencies {
                rooted_read: None,
                membership: HashSet::new(),
                products: IndexMap::from([(external.clone(), Some(2))]),
                facts: HashMap::from([(fact.clone(), if discordant_fact { fact_two } else { fact_one })]),
            };
            assert!(memo.begin(left.clone()));
            memo.unblock(ProductRequestId(NonZeroU64::MIN), &left, left_dependencies.clone());
            assert!(memo.begin(right.clone()));
            let mut entries = vec![
                (left.clone(), ProductValue::Unit, left_dependencies),
                (right.clone(), ProductValue::Unit, right_dependencies),
            ];
            if reverse {
                entries.reverse();
            }

            assert!(!finish_test_group(&mut memo, &tel, &left, entries, &fake_types()));
            for key in [&left, &right] {
                assert!(memo.get(key).is_none());
                assert!(!memo.pending_dependencies.contains_key(key));
                assert!(!memo.in_progress.contains(key));
            }
            assert!(
                memo.product_readers
                    .get(&external)
                    .is_none_or(|readers| !readers.contains(&left) && !readers.contains(&right))
            );
            assert!(
                memo.fact_readers
                    .get(fact.fact())
                    .is_none_or(|readers| !readers.contains(&left) && !readers.contains(&right))
            );
            assert_eq!(memo.generation(&unrelated), unrelated_generation);

            for key in [&left, &right] {
                assert!(memo.begin(key.clone()));
            }
            let concordant = ProductDependencies {
                rooted_read: None,
                membership: HashSet::new(),
                products: IndexMap::from([(external.clone(), Some(2))]),
                facts: HashMap::from([(fact.clone(), fact_two)]),
            };
            assert!(finish_test_group(
                &mut memo,
                &tel,
                &left,
                vec![
                    (left.clone(), ProductValue::Unit, concordant.clone()),
                    (right.clone(), ProductValue::Unit, concordant),
                ],
                &fake_types(),
            ));
        }
    }
}

#[test]
fn rejected_group_retries_without_displaced_dependency_snapshots() {
    let types = fake_types();
    let root = RootId::for_test(42);
    let left = ProductKey::AbiExecutable(fake_executable_with_function(root, 420));
    let right = ProductKey::AbiExecutable(fake_executable_with_function(root, 421));
    let external = ProductKey::AbiExecutable(fake_executable_with_function(root, 422));

    for reverse in [false, true] {
        let mut memo = ProductMemo::default();
        let tel = ConfiguredTelemetry::new();
        for key in [&left, &right] {
            assert!(memo.begin(key.clone()));
        }
        let first = ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::from([(external.clone(), Some(1))]),
            facts: HashMap::new(),
        };
        assert!(finish_test_group(
            &mut memo,
            &tel,
            &left,
            vec![
                (left.clone(), ProductValue::Unit, first.clone()),
                (right.clone(), ProductValue::Unit, first),
            ],
            &types,
        ));
        for key in [&left, &right] {
            memo.remove(&tel, key, &types);
        }

        assert!(memo.begin(right.clone()));
        let current = ProductDependencies {
            rooted_read: None,
            membership: HashSet::new(),
            products: IndexMap::from([(external.clone(), Some(2))]),
            facts: HashMap::new(),
        };
        memo.unblock(ProductRequestId(NonZeroU64::MIN), &right, current.clone());
        assert!(memo.begin(left.clone()));
        let stale = memo
            .displaced
            .get(&left)
            .expect("left should retain its prior value while reproducing")
            .dependencies
            .as_ref()
            .clone();
        let mut entries = vec![
            (left.clone(), ProductValue::Unit, stale),
            (right.clone(), ProductValue::Unit, current.clone()),
        ];
        if reverse {
            entries.reverse();
        }
        assert!(!finish_test_group(&mut memo, &tel, &left, entries, &types));

        for key in [&left, &right] {
            let displaced = memo
                .displaced
                .get(key)
                .expect("rejected member should retain its prior value and generation");
            assert_eq!(displaced.generation, 1);
            assert_eq!(*displaced.dependencies, ProductDependencies::default());
            assert!(memo.begin(key.clone()));
        }
        assert!(finish_test_group(
            &mut memo,
            &tel,
            &left,
            vec![
                (left.clone(), ProductValue::Unit, current.clone()),
                (right.clone(), ProductValue::Unit, current),
            ],
            &types,
        ));
        assert_eq!(memo.generation(&left), Some(1));
        assert_eq!(memo.generation(&right), Some(1));
    }
}

#[test]
fn callable_owner_scc_is_finite_order_free_and_contains_only_pass_through_owners() {
    let root = RootId::for_test(36);
    let x = TransportPosition::ExecutableInput {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 360)),
        semantic_index: 1,
    };
    let left = TransportPosition::Value {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 361)),
        value: ValueId::from_u32(1),
    };
    let right = TransportPosition::Value {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 361)),
        value: ValueId::from_u32(2),
    };
    let left_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 362));
    let right_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 363));
    let x_layout = TransportLayout {
        structural: ShapeId::for_test(91),
        carrier: TransportCarrier::ValueRef(LaneId::for_test(0)),
    };
    let y_layout = TransportLayout::structural(ShapeId::for_test(92));
    let no_anchor = [OwnerEquation {
        seed: OwnerState::bottom(x_layout),
        children: vec![0],
    }];
    assert_eq!(
        settle_owner_equations(&no_anchor, false).0[0],
        OwnerState::bottom(x_layout)
    );

    let seed = OwnerState {
        layout: x_layout,
        resolutions: HashSet::from([left_resolution.clone(), left_resolution, right_resolution]),
        publications: HashSet::from([x, left, right]),
    };
    let pair = [
        OwnerEquation {
            seed: seed.clone(),
            children: vec![1],
        },
        OwnerEquation {
            seed: OwnerState::bottom(y_layout),
            children: vec![0],
        },
    ];
    let pair_forward = settle_owner_equations(&pair, false);
    let pair_reverse = settle_owner_equations(&pair, true);
    assert_eq!(pair_forward.0, pair_reverse.0);
    assert!(pair_forward.1 <= 3 && pair_reverse.1 <= 3);
    assert_eq!(pair_forward.0[0].layout, x_layout);
    assert_eq!(pair_forward.0[1].layout, y_layout);

    let ring = [
        OwnerEquation {
            seed,
            children: vec![1],
        },
        OwnerEquation {
            seed: OwnerState::bottom(y_layout),
            children: vec![2],
        },
        OwnerEquation {
            seed: OwnerState::bottom(x_layout),
            children: vec![3],
        },
        OwnerEquation {
            seed: OwnerState::bottom(y_layout),
            children: vec![0],
        },
    ];
    let ring_forward = settle_owner_equations(&ring, false);
    let ring_reverse = settle_owner_equations(&ring, true);
    assert_eq!(ring_forward.0, ring_reverse.0);
    assert!(ring_forward.1 <= 5 && ring_reverse.1 <= 5);

    let mut world = World::new();
    let callable = world.intern_callable(super::super::transport::CallableDescr {
        function: None,
        arity: 0,
        capture_layouts: Box::default(),
    });
    for answer in pair_forward.0 {
        let ProductValue::CallableConstruction(answer) = answer.product_value(callable, BoundaryId::for_test(9)) else {
            unreachable!()
        };
        assert!(answer.construction.is_none());
        assert_eq!(answer.callable_facts[&callable].resolutions.len(), 2);
        assert_eq!(answer.callable_facts[&callable].direct_edges.len(), 2);
        assert_eq!(answer.boundary_facts[&BoundaryId::for_test(9)].publications.len(), 3);
    }
}

#[test]
fn callable_owner_group_is_atomic_replacement_safe_and_frontier_relative() {
    let types = fake_types();
    let root = RootId::for_test(37);
    let x_position = TransportPosition::ExecutableInput {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 370)),
        semantic_index: 1,
    };
    let y_position = TransportPosition::Value {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 370)),
        value: ValueId::from_u32(5),
    };
    let terminal_position = TransportPosition::Value {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 371)),
        value: ValueId::from_u32(1),
    };
    let x = ProductKey::CallableConstruction(x_position.clone());
    let y = ProductKey::CallableConstruction(y_position);
    let terminal = ProductKey::CallableConstruction(terminal_position.clone());
    let slot = ProductKey::TransportShape(x_position.clone());
    let parent = ProductKey::AbiExecutable(fake_executable_with_function(root, 370));
    let unrelated = ProductKey::CallableConstruction(TransportPosition::Value {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 372)),
        value: ValueId::from_u32(0),
    });
    let unrelated_parent = ProductKey::AbiExecutable(fake_executable_with_function(root, 372));
    let mut world = World::new();
    let callable = world.intern_callable(super::super::transport::CallableDescr {
        function: None,
        arity: 0,
        capture_layouts: Box::default(),
    });
    let boundary = BoundaryId::for_test(10);
    let layout = TransportLayout {
        structural: ShapeId::for_test(101),
        carrier: TransportCarrier::ValueRef(LaneId::for_test(0)),
    };
    let first_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 373));
    let second_resolution = executable_symbol_for_test(&fake_executable_with_function(root, 374));
    let equations = |resolution: ExecutableSymbol, publication: TransportPosition| {
        [
            OwnerEquation {
                seed: OwnerState {
                    layout,
                    resolutions: HashSet::from([resolution]),
                    publications: HashSet::from([publication, x_position.clone()]),
                },
                children: vec![1],
            },
            OwnerEquation {
                seed: OwnerState::bottom(layout),
                children: vec![0],
            },
        ]
    };
    let first_answers =
        settle_owner_equations(&equations(first_resolution.clone(), terminal_position.clone()), false).0;
    let keys = [x.clone(), y.clone()];
    let external = [terminal.clone(), slot.clone()];
    let slot_value = ProductValue::TransportShape(TransportShapeFact::Layout(layout));

    let mut memos = Vec::new();
    for reverse in [false, true] {
        let mut memo = ProductMemo::default();
        finish_test_product(
            &mut memo,
            &terminal,
            callable_owner_answer(
                layout,
                terminal_position.clone(),
                callable,
                boundary,
                first_resolution.clone(),
            ),
            [],
        );
        finish_test_product(&mut memo, &slot, slot_value.clone(), []);
        finish_owner_group(&mut memo, &keys, &first_answers, &external, callable, boundary, reverse);
        memos.push(memo);
    }
    let mut memo = memos.remove(0);
    let reverse = memos.remove(0);
    let tel = ConfiguredTelemetry::new();
    for key in &keys {
        assert_eq!(memo.get(key), reverse.get(key));
        assert_eq!(memo.generation(key), reverse.generation(key));
        assert_eq!(
            memo.product_dependencies(key),
            Some(
                &keys
                    .iter()
                    .chain([&terminal, &slot])
                    .map(|dependency| (dependency.clone(), Some(1)))
                    .collect::<IndexMap<_, _>>()
            )
        );
    }

    finish_test_product(&mut memo, &parent, ProductValue::Unit, [x.clone()]);
    finish_test_product(&mut memo, &unrelated, withdrawn_callable_owner_answer(layout), []);
    finish_test_product(&mut memo, &unrelated_parent, ProductValue::Unit, [unrelated.clone()]);
    let unrelated_generations = (memo.generation(&unrelated), memo.generation(&unrelated_parent));

    let generations = keys.clone().map(|key| memo.generation(&key));
    for key in &keys {
        memo.remove(&tel, key, &types);
    }
    finish_owner_group(&mut memo, &keys, &first_answers, &external, callable, boundary, true);
    assert_eq!(keys.clone().map(|key| memo.generation(&key)), generations);

    let replacement_position = TransportPosition::Value {
        executable: executable_symbol_for_test(&fake_executable_with_function(root, 371)),
        value: ValueId::from_u32(2),
    };
    memo.remove(&tel, &terminal, &types);
    finish_test_product(
        &mut memo,
        &terminal,
        callable_owner_answer(
            layout,
            replacement_position.clone(),
            callable,
            boundary,
            second_resolution.clone(),
        ),
        [],
    );
    assert!(keys.iter().all(|key| memo.get(key).is_none()));
    assert!(memo.stale_dependency(&tel, &parent, &types).is_some());
    let replacement_answers = settle_owner_equations(
        &equations(second_resolution.clone(), replacement_position.clone()),
        true,
    )
    .0;
    finish_owner_group(
        &mut memo,
        &keys,
        &replacement_answers,
        &external,
        callable,
        boundary,
        false,
    );
    assert!(keys.iter().all(|key| memo.generation(key) == Some(2)));
    assert!(memo.get(&parent).is_none());

    memo.remove(&tel, &terminal, &types);
    finish_test_product(
        &mut memo,
        &terminal,
        callable_owner_answer(layout, replacement_position, callable, boundary, second_resolution),
        [],
    );
    assert!(keys.iter().all(|key| memo.generation(key) == Some(2)));

    memo.remove(&tel, &terminal, &types);
    finish_test_product(&mut memo, &terminal, withdrawn_callable_owner_answer(layout), []);
    assert!(keys.iter().all(|key| memo.get(key).is_none()));
    let empty = settle_owner_equations(
        &equations(
            executable_symbol_for_test(&fake_executable_with_function(root, 376)),
            x_position.clone(),
        ),
        false,
    )
    .0
    .into_iter()
    .map(|answer| OwnerState::bottom(answer.layout))
    .collect::<Vec<_>>();
    finish_owner_group(&mut memo, &keys, &empty, &external, callable, boundary, false);
    assert!(keys.iter().all(|key| memo.generation(key) == Some(3)));

    memo.remove(&tel, &slot, &types);
    finish_test_product(
        &mut memo,
        &slot,
        ProductValue::TransportShape(TransportShapeFact::Layout(TransportLayout {
            structural: ShapeId::for_test(102),
            ..layout
        })),
        [],
    );
    assert!(keys.iter().all(|key| memo.get(key).is_none()));
    finish_owner_group(
        &mut memo,
        std::slice::from_ref(&x),
        std::slice::from_ref(&empty[0]),
        &external,
        callable,
        boundary,
        false,
    );
    assert!(memo.get(&x).is_some());
    assert!(memo.get(&y).is_none());
    assert_eq!(
        (memo.generation(&unrelated), memo.generation(&unrelated_parent)),
        unrelated_generations
    );
}
