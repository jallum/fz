#[derive(Clone)]
enum OwnershipFormula {
    Value(ProductValue),
    Copy(ProductKey),
    Reader {
        selector: ProductKey,
        child: ProductKey,
        recursive: bool,
        value: ProductValue,
    },
    Recursive {
        child: ProductKey,
        peer: ProductKey,
    },
    RecursiveMembership {
        member: ProductKey,
        peer: ProductKey,
    },
    Membership {
        selector: ProductKey,
        child: ProductKey,
    },
    Seed(Vec<ProductKey>, ProductValue),
    FactMembership {
        fact: FactKey,
        state: FactState,
        children: Vec<ProductKey>,
    },
    FactRoot {
        fact: FactKey,
        state: FactState,
        seed: ProductKey,
    },
    DeliverMembershipFact {
        fact: FactKey,
        owner: ProductKey,
        children: Vec<ProductKey>,
    },
    Root(ProductKey),
    PrefixRoot(Vec<ProductKey>, ProductKey),
    SelectedRoot {
        selector: ProductKey,
        selected: ProductKey,
        otherwise: ProductKey,
    },
    RootControlledChild {
        seed: ProductKey,
        child: ProductKey,
        select_from_data: bool,
    },
    Unavailable,
}

struct OwnershipProducers<'a> {
    telemetry: &'a ConfiguredTelemetry,
    types: super::super::Types,
    formulas: HashMap<ProductKey, OwnershipFormula>,
    calls: Vec<ProductKey>,
}

impl ProductProducers for OwnershipProducers<'_> {
    fn product_types(&self) -> &super::super::Types {
        &self.types
    }

    fn produce(&mut self, context: &mut ProductReadContext<'_>, key: &ProductKey) -> PullOutcome {
        self.calls.push(key.clone());
        let tel = self.telemetry;
        let formula = self.formulas[key].clone();
        match formula {
            OwnershipFormula::FactRoot { fact, state, seed } => {
                context.dependencies.facts.insert(FactUse::settled(fact), state);
                match context.read_rooted_products(tel, key.clone(), seed, &self.types) {
                    Ok(_) => PullOutcome::Produced(ProductValue::Unit),
                    Err(waits) => PullOutcome::Waiting(waits),
                }
            }
            OwnershipFormula::FactMembership { fact, state, children } => {
                context.dependencies.facts.insert(FactUse::settled(fact), state);
                for child in children {
                    context.include_product(child);
                }
                PullOutcome::Produced(ProductValue::Unit)
            }
            OwnershipFormula::DeliverMembershipFact { fact, owner, children } => {
                let state = FactState {
                    revision: Some(2),
                    settled: true,
                };
                context.session.apply_fact_movements(&[FactMovement {
                    key: fact.clone(),
                    state,
                }]);
                self.formulas
                    .insert(owner, OwnershipFormula::FactMembership { fact, state, children });
                self.formulas
                    .insert(key.clone(), OwnershipFormula::Value(ProductValue::Unit));
                PullOutcome::Produced(ProductValue::Unit)
            }
            OwnershipFormula::Seed(children, value) => {
                for child in children {
                    context.include_product(child);
                }
                PullOutcome::Produced(value)
            }
            OwnershipFormula::Root(seed) => match context.read_rooted_products(tel, key.clone(), seed, &self.types) {
                Ok(_) => PullOutcome::Produced(ProductValue::Unit),
                Err(waits) => PullOutcome::Waiting(waits),
            },
            OwnershipFormula::PrefixRoot(prefix, seed) => {
                for control in prefix {
                    if context.read_product(tel, control.clone(), &self.types).is_none() {
                        return PullOutcome::wait_on_product(control);
                    }
                }
                match context.read_rooted_products(tel, key.clone(), seed, &self.types) {
                    Ok(_) => PullOutcome::Produced(ProductValue::Unit),
                    Err(waits) => PullOutcome::Waiting(waits),
                }
            }
            OwnershipFormula::SelectedRoot {
                selector,
                selected,
                otherwise,
            } => {
                let Some(ProductValue::ExecutableEffects(choice)) =
                    context.read_product(tel, selector.clone(), &self.types)
                else {
                    return PullOutcome::wait_on_product(selector);
                };
                let seed = if choice.allocates { selected } else { otherwise };
                match context.read_rooted_products(tel, key.clone(), seed, &self.types) {
                    Ok(_) => PullOutcome::Produced(ProductValue::Unit),
                    Err(waits) => PullOutcome::Waiting(waits),
                }
            }
            OwnershipFormula::RootControlledChild {
                seed,
                child,
                select_from_data,
            } => {
                let rooted = context.read_rooted_products(tel, key.clone(), seed, &self.types);
                let selected = if select_from_data {
                    rooted.as_ref().is_ok_and(|changes| {
                        changes.iter().any(|(_, value)| {
                        matches!(value, Some(ProductValue::ExecutableEffects(effects)) if effects.allocates)
                    })
                    })
                } else {
                    rooted.is_err()
                };
                if selected && context.read_product(tel, child.clone(), &self.types).is_none() {
                    return match rooted {
                        Ok(_) => PullOutcome::wait_on_product(child),
                        Err(waits) => PullOutcome::Waiting(waits),
                    };
                }
                match rooted {
                    Ok(_) => PullOutcome::Produced(ProductValue::Unit),
                    Err(waits) => PullOutcome::Waiting(waits),
                }
            }
            OwnershipFormula::Membership { selector, child } => {
                let Some(ProductValue::ExecutableEffects(selected)) =
                    context.read_product(tel, selector.clone(), &self.types)
                else {
                    return PullOutcome::wait_on_product(selector);
                };
                if selected.allocates {
                    context.include_product(child);
                }
                PullOutcome::Produced(ProductValue::Unit)
            }
            OwnershipFormula::Value(value) => PullOutcome::Produced(value),
            OwnershipFormula::Unavailable => PullOutcome::Failed(ProductFailure::NativeLowering),
            OwnershipFormula::Copy(child) => match context.read_product(tel, child.clone(), &self.types) {
                Some(value) => PullOutcome::Produced(value.clone()),
                None => PullOutcome::wait_on_product(child),
            },
            OwnershipFormula::Reader {
                selector,
                child,
                recursive,
                value,
            } => {
                let Some(ProductValue::ExecutableEffects(selected)) =
                    context.read_product(tel, selector.clone(), &self.types)
                else {
                    return PullOutcome::wait_on_product(selector);
                };
                if !selected.allocates {
                    return PullOutcome::Produced(value);
                }
                if recursive {
                    ownership_recursive_read(context, tel, key, child, value, &self.types)
                } else if context.read_product(tel, child.clone(), &self.types).is_none() {
                    PullOutcome::wait_on_product(child)
                } else {
                    PullOutcome::Produced(value)
                }
            }
            OwnershipFormula::Recursive { child, peer } => {
                let Some(value) = context.read_product(tel, child.clone(), &self.types).cloned() else {
                    return PullOutcome::wait_on_product(child);
                };
                ownership_recursive_read(context, tel, key, peer, value, &self.types)
            }
            OwnershipFormula::RecursiveMembership { member, peer } => {
                context.include_product(member);
                ownership_recursive_read(context, tel, key, peer, ProductValue::Unit, &self.types)
            }
        }
    }
}

fn ownership_recursive_read(
    context: &mut ProductReadContext<'_>,
    tel: &ConfiguredTelemetry,
    key: &ProductKey,
    peer: ProductKey,
    value: ProductValue,
    types: &super::super::Types,
) -> PullOutcome {
    match context.read_recursive_product(tel, peer.clone(), key, types) {
        RecursiveProductRead::Ready(value) => PullOutcome::Produced(value.clone()),
        RecursiveProductRead::Waiting => PullOutcome::wait_on_product(peer),
        RecursiveProductRead::Group(members) => {
            let value = context
                .recorded_recursive_group_inputs(key, &members, types)
                .into_iter()
                .find_map(|(_, value)| value.filter(|value| matches!(value, ProductValue::MaterializedExecutable(_))))
                .unwrap_or(value);
            let values = vec![value; members.len()];
            PullOutcome::Produced(context.stage_recursive_group(key, &members, values))
        }
    }
}

fn ownership_pull(
    driver: &mut ProductDriver<'_, ConfiguredTelemetry>,
    producers: &mut OwnershipProducers,
    root: &ProductKey,
) -> PullOutcome {
    let mut world = World::new();
    let session_root = driver.session().root();
    match super::super::product_drive::drive_root_product_with_producers::<_, String>(
        &mut world,
        driver.tel,
        session_root,
        root.clone(),
        driver,
        None,
        producers,
    ) {
        Ok(value) => PullOutcome::Produced(value),
        Err(_) => PullOutcome::Failed(ProductFailure::NativeLowering),
    }
}

#[test]
fn recursive_completion_preserves_each_pending_members_current_membership() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(901);
    let [left, right, left_child, right_child] =
        [1, 2, 3, 4].map(|function| ProductKey::ExecutableEffects(fake_executable_with_function(root, function)));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        formulas: HashMap::from([
            (
                left.clone(),
                OwnershipFormula::RecursiveMembership {
                    member: left_child.clone(),
                    peer: right.clone(),
                },
            ),
            (
                right.clone(),
                OwnershipFormula::RecursiveMembership {
                    member: right_child.clone(),
                    peer: left.clone(),
                },
            ),
        ]),
        calls: Vec::new(),
    };
    let mut driver = ProductDriver::new(&tel, root);
    assert!(matches!(
        ownership_pull(&mut driver, &mut producers, &left),
        PullOutcome::Produced(_)
    ));
    assert_eq!(
        driver.session().memo.produced[&left].membership,
        HashSet::from([left_child])
    );
    assert_eq!(
        driver.session().memo.produced[&right].membership,
        HashSet::from([right_child])
    );
}

#[test]
fn recursive_publication_exposes_a_child_once_after_all_owning_gates_clear() {
    let tel = ConfiguredTelemetry::new();
    let events = Rc::new(RefCell::new(Vec::new()));
    let requests = Rc::clone(&events);
    tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(PRODUCT_REQUESTED_EVENT, move |_, _, _, key, _| {
        requests.borrow_mut().push((false, key.clone()))
    });
    let settlements = Rc::clone(&events);
    tel.attach_raw_event3::<ProductKey, ProductValue, ProductSettlement, _>(
        &["fz", "compiler2", "pull", "product", "settled"],
        move |_, _, _, key, _, _| settlements.borrow_mut().push((true, key.clone())),
    );
    let [child, right, left, packaging] = [0, 1, 2, 3].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        calls: Vec::new(),
        formulas: HashMap::from([
            (
                left.clone(),
                OwnershipFormula::RecursiveMembership {
                    member: right.clone(),
                    peer: right.clone(),
                },
            ),
            (
                right.clone(),
                OwnershipFormula::RecursiveMembership {
                    member: child.clone(),
                    peer: left.clone(),
                },
            ),
            (child.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (packaging.clone(), OwnershipFormula::Root(left.clone())),
        ]),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(913));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    driver.session_mut().memo.invalidate_products(
        &tel,
        [left.clone(), right.clone(), child.clone(), packaging.clone()],
        &producers.types,
    );
    events.borrow_mut().clear();
    producers.calls.clear();
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(producers.calls.iter().filter(|key| *key == &child).count(), 1);
    let recorded = events.borrow();
    let child_request = recorded
        .iter()
        .position(|(settled, key)| !settled && key == &child)
        .unwrap();
    let right_settle = recorded
        .iter()
        .position(|(settled, key)| *settled && key == &right)
        .unwrap();
    let left_settle = recorded
        .iter()
        .position(|(settled, key)| *settled && key == &left)
        .unwrap();
    assert!(
        right_settle < left_settle && left_settle < child_request,
        "clearing the inner owner first cannot admit through its still-dirty outer gate mid-publication"
    );
    assert_eq!(
        recorded
            .iter()
            .filter(|(settled, key)| !settled && key == &packaging)
            .count(),
        2
    );
    drop(recorded);
    producers.calls.clear();
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(producers.calls.is_empty());
}

#[test]
fn recursive_publication_cancels_old_suffix_owned_admissions_before_exposing_children() {
    let tel = ConfiguredTelemetry::new();
    let events = Rc::new(RefCell::new(Vec::new()));
    let requests = Rc::clone(&events);
    tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(PRODUCT_REQUESTED_EVENT, move |_, _, _, key, _| {
        requests.borrow_mut().push((false, key.clone()))
    });
    let evaluations = Rc::clone(&events);
    tel.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
        PRODUCT_EVALUATED_EVENT,
        move |_, _, _, key, _, _| evaluations.borrow_mut().push((true, key.clone())),
    );
    let [seed, member, suffix, child, packaging] =
        [0, 1, 2, 3, 4].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        calls: Vec::new(),
        formulas: HashMap::from([
            (
                seed.clone(),
                OwnershipFormula::Seed(vec![member.clone()], ProductValue::Unit),
            ),
            (
                member.clone(),
                OwnershipFormula::RecursiveMembership {
                    member: child.clone(),
                    peer: suffix.clone(),
                },
            ),
            (
                suffix.clone(),
                OwnershipFormula::RecursiveMembership {
                    member: child.clone(),
                    peer: member,
                },
            ),
            (child.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (
                packaging.clone(),
                OwnershipFormula::RootControlledChild {
                    seed: seed.clone(),
                    child: suffix,
                    select_from_data: false,
                },
            ),
        ]),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(914));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &seed),
        PullOutcome::Produced(ProductValue::Unit)
    );
    events.borrow_mut().clear();
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    let recorded = events.borrow();
    let child_request = recorded
        .iter()
        .position(|(evaluated, key)| !evaluated && key == &child)
        .unwrap();
    assert_eq!(
        recorded[..child_request]
            .iter()
            .filter(|(evaluated, key)| *evaluated && key == &packaging)
            .count(),
        2,
        "group publication invalidates the already observed suffix, so fresh root control precedes queued child demand"
    );
    assert_eq!(producers.calls.iter().filter(|key| *key == &child).count(), 1);
}

#[test]
fn rooted_maintenance_is_reported_by_the_request_that_performs_it() {
    let tel = ConfiguredTelemetry::new();
    let recorded = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&recorded);
    tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
        &["fz", "compiler2", "pull", "product", "validation"],
        move |_, _, _, _, work| observed.borrow_mut().push(*work),
    );
    let root = RootId::for_test(902);
    let seed = ProductKey::ExecutableEffects(fake_executable_with_function(root, 1));
    let packaging = ProductKey::RootBackendProduct(root);
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        formulas: HashMap::from([
            (seed.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (packaging.clone(), OwnershipFormula::Root(seed.clone())),
        ]),
        calls: Vec::new(),
    };
    let mut driver = ProductDriver::new(&tel, root);
    assert!(matches!(
        ownership_pull(&mut driver, &mut producers, &seed),
        PullOutcome::Produced(_)
    ));
    assert!(matches!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(_)
    ));
    assert_eq!(
        recorded.borrow().iter().map(|work| work.witness_updates).sum::<u64>(),
        3,
        "one sparse node insertion, one mark and one disposal"
    );
    let count = recorded.borrow().len();
    assert!(matches!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(_)
    ));
    assert_eq!(
        recorded.borrow().len(),
        count,
        "unchanged request emits no prior maintenance"
    );
}

#[test]
fn replacing_or_retiring_a_waiting_witness_reports_its_disposal() {
    for retire in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let recorded = Rc::new(RefCell::new(Vec::new()));
        let observed = Rc::clone(&recorded);
        tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
            &["fz", "compiler2", "pull", "product", "validation"],
            move |_, _, _, _, work| observed.borrow_mut().push(*work),
        );
        let root = RootId::for_test(903);
        let [old, current] = [1, 2].map(|id| ProductKey::ExecutableEffects(fake_executable_with_function(root, id)));
        let packaging = ProductKey::RootBackendProduct(root);
        let mut producers = OwnershipProducers {
            telemetry: &tel,
            types: fake_types(),
            formulas: HashMap::from([
                (old.clone(), OwnershipFormula::Unavailable),
                (current.clone(), OwnershipFormula::Value(ProductValue::Unit)),
                (packaging.clone(), OwnershipFormula::Root(old)),
            ]),
            calls: Vec::new(),
        };
        let mut driver = ProductDriver::new(&tel, root);
        assert!(matches!(
            ownership_pull(&mut driver, &mut producers, &current),
            PullOutcome::Produced(_)
        ));
        assert!(matches!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Failed(_)
        ));
        producers.formulas.insert(
            packaging.clone(),
            if retire {
                OwnershipFormula::Value(ProductValue::Unit)
            } else {
                OwnershipFormula::Root(current)
            },
        );
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [packaging.clone()], &producers.types);
        recorded.borrow_mut().clear();
        assert!(matches!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(_)
        ));
        assert_eq!(
            recorded.borrow().iter().map(|work| work.witness_updates).sum::<u64>(),
            if retire { 1 } else { 4 },
            "the discarded waiting witness is accounted together with its replacement"
        );
    }
}

fn ownership_selected(selected: bool) -> ProductValue {
    ProductValue::ExecutableEffects(EffectSummary {
        allocates: selected,
        ..EffectSummary::default()
    })
}

#[test]
fn validation_reports_work_even_when_no_dirty_vertex_is_checked() {
    let tel = ConfiguredTelemetry::new();
    let recorded = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&recorded);
    tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
        &["fz", "compiler2", "pull", "product", "validation"],
        move |_, _, _, _, work| observed.borrow_mut().push(*work),
    );
    let mut memo = ProductMemo::default();
    let key = ProductKey::RootBackendProduct(RootId::for_test(190));
    let work = ProductValidation {
        edge_scans: 1,
        ..ProductValidation::default()
    };
    memo.finish_validation(
        &tel,
        ProductValidationWalk {
            work,
            ..ProductValidationWalk::default()
        },
        false,
        None,
        &fake_types(),
    )
    .report(&tel, &key);
    assert_eq!(*recorded.borrow(), vec![work]);
}

#[test]
fn a_successful_formula_without_a_rooted_read_retires_only_its_own_witness() {
    let tel = ConfiguredTelemetry::new();
    let key = |id| ProductKey::RootBackendProduct(RootId::for_test(id));
    let [seed, retired, retained] = [0, 1, 2].map(key);
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        calls: Vec::new(),
        formulas: HashMap::from([
            (seed.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (retired.clone(), OwnershipFormula::Root(seed.clone())),
            (retained.clone(), OwnershipFormula::Root(seed.clone())),
        ]),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(191));
    for root in [&retired, &retained] {
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, root),
            PullOutcome::Produced(ProductValue::Unit)
        );
    }
    producers
        .formulas
        .insert(retired.clone(), OwnershipFormula::Value(ProductValue::Unit));
    driver
        .session_mut()
        .memo
        .invalidate_products(&tel, [retired.clone()], &producers.types);
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &retired),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(
        !driver.session().memo.rooted.contains_key(&retired),
        "accepted current observations replace old witness ownership"
    );
    assert_eq!(
        driver.session().memo.rooted_readers[&seed],
        HashSet::from([retained.clone()])
    );
    producers.calls.clear();
    producers.formulas.insert(seed.clone(), OwnershipFormula::Unavailable);
    driver
        .session_mut()
        .memo
        .invalidate_products(&tel, [seed], &producers.types);
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &retired),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(
        producers.calls.is_empty(),
        "movement in a retired witness is unrelated to this formula"
    );
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &retained),
        PullOutcome::Failed(ProductFailure::NativeLowering)
    );
}

#[test]
fn current_root_control_replaces_a_retained_or_waiting_membership_observation() {
    for indirect in [false, true] {
        for waiting in [false, true] {
            let tel = ConfiguredTelemetry::new();
            let key = |id| ProductKey::RootBackendProduct(RootId::for_test(id));
            let [old_seed, new_seed, selector, packaging] = [0, 1, 2, 3].map(key);
            let input = if indirect { key(4) } else { selector.clone() };
            let mut producers = OwnershipProducers {
                telemetry: &tel,
                types: fake_types(),
                calls: Vec::new(),
                formulas: HashMap::from([
                    (old_seed.clone(), OwnershipFormula::Value(ProductValue::Unit)),
                    (new_seed.clone(), OwnershipFormula::Value(ProductValue::Unit)),
                    (selector.clone(), OwnershipFormula::Value(ownership_selected(true))),
                    (
                        packaging.clone(),
                        OwnershipFormula::SelectedRoot {
                            selector: selector.clone(),
                            selected: old_seed.clone(),
                            otherwise: new_seed,
                        },
                    ),
                ]),
            };
            if indirect {
                producers
                    .formulas
                    .insert(selector.clone(), OwnershipFormula::Copy(input.clone()));
                producers
                    .formulas
                    .insert(input.clone(), OwnershipFormula::Value(ownership_selected(true)));
            }
            let mut driver = ProductDriver::new(&tel, RootId::for_test(186));
            assert_eq!(
                ownership_pull(&mut driver, &mut producers, &packaging),
                PullOutcome::Produced(ProductValue::Unit)
            );
            driver
                .session_mut()
                .memo
                .invalidate_products(&tel, [old_seed.clone()], &producers.types);
            if waiting {
                driver
                    .session_mut()
                    .memo
                    .invalidate_products(&tel, [packaging.clone()], &producers.types);
                assert_eq!(
                    driver.pull(&mut producers, packaging.clone()),
                    PullOutcome::wait_on_product(old_seed.clone())
                );
                assert!(driver.session().memo.pending_dependencies.contains_key(&packaging));
            }
            producers.calls.clear();
            producers
                .formulas
                .insert(old_seed.clone(), OwnershipFormula::Unavailable);
            producers
                .formulas
                .insert(input.clone(), OwnershipFormula::Value(ownership_selected(false)));
            driver
                .session_mut()
                .memo
                .invalidate_products(&tel, [input], &producers.types);
            if waiting {
                assert_eq!(
                    driver.pull(&mut producers, packaging.clone()),
                    PullOutcome::wait_on_product(selector.clone())
                );
                assert_eq!(
                    driver.session().memo.pending_dependencies[&packaging]
                        .dependencies
                        .rooted_read,
                    None,
                    "waiting on an earlier control is not a current rooted observation"
                );
            }
            assert_eq!(
                ownership_pull(&mut driver, &mut producers, &packaging),
                PullOutcome::Produced(ProductValue::Unit),
                "waiting={waiting}; calls={:?}",
                producers.calls
            );
            assert!(
                !producers.calls.contains(&old_seed),
                "current controls must withdraw the obsolete seed before demand; waiting={waiting}"
            );
        }
    }
}

#[test]
fn changed_rooted_data_or_readiness_replays_control_before_a_pending_suffix() {
    for select_from_data in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let key = |id| ProductKey::RootBackendProduct(RootId::for_test(id));
        let [seed, upstream, child, packaging] = [0, 1, 2, 3].map(key);
        let mut producers = OwnershipProducers {
            telemetry: &tel,
            types: fake_types(),
            calls: Vec::new(),
            formulas: HashMap::from([
                (seed.clone(), OwnershipFormula::Value(ownership_selected(true))),
                (upstream.clone(), OwnershipFormula::Value(ProductValue::Unit)),
                (child.clone(), OwnershipFormula::Copy(upstream.clone())),
                (
                    packaging.clone(),
                    OwnershipFormula::RootControlledChild {
                        seed: seed.clone(),
                        child: child.clone(),
                        select_from_data,
                    },
                ),
            ]),
        };
        let mut driver = ProductDriver::new(&tel, RootId::for_test(187));
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &child),
            PullOutcome::Produced(ProductValue::Unit)
        );
        if select_from_data {
            assert_eq!(
                ownership_pull(&mut driver, &mut producers, &seed),
                PullOutcome::Produced(ownership_selected(true))
            );
        }
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [upstream.clone()], &producers.types);
        assert!(matches!(
            driver.pull(&mut producers, packaging.clone()),
            PullOutcome::Waiting(_)
        ));
        assert!(
            driver.session().memo.pending_dependencies[&packaging]
                .dependencies
                .rooted_read
                .is_some()
        );
        producers.calls.clear();
        producers.formulas.insert(upstream, OwnershipFormula::Unavailable);
        producers
            .formulas
            .insert(seed.clone(), OwnershipFormula::Value(ownership_selected(false)));
        assert!(finish_test_entry(
            &mut driver.session_mut().memo,
            &tel,
            &seed,
            ownership_selected(false),
            ProductDependencies::default(),
            &producers.types
        ));
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit),
            "select_from_data={select_from_data}; calls={:?}",
            producers.calls
        );
        assert!(
            !producers.calls.contains(&child),
            "rooted control must retire its obsolete suffix"
        );
    }
}

#[test]
fn a_waiting_formula_does_not_acknowledge_delivered_rooted_changes() {
    let tel = ConfiguredTelemetry::new();
    let key = |id| ProductKey::RootBackendProduct(RootId::for_test(id));
    let [seed, upstream, child, packaging] = [0, 1, 2, 3].map(key);
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        calls: Vec::new(),
        formulas: HashMap::from([
            (seed.clone(), OwnershipFormula::Value(ownership_selected(true))),
            (upstream.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (child.clone(), OwnershipFormula::Copy(upstream.clone())),
            (
                packaging.clone(),
                OwnershipFormula::RootControlledChild {
                    seed: seed.clone(),
                    child: child.clone(),
                    select_from_data: true,
                },
            ),
        ]),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(188));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &child),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &seed),
        PullOutcome::Produced(ownership_selected(true))
    );
    driver
        .session_mut()
        .memo
        .invalidate_products(&tel, [upstream.clone()], &producers.types);
    assert_eq!(
        driver.pull(&mut producers, packaging.clone()),
        PullOutcome::wait_on_product(child.clone())
    );
    assert_eq!(
        driver.pull(&mut producers, packaging.clone()),
        PullOutcome::wait_on_product(child),
        "a retried formula must still receive changes which its waiting attempt did not publish"
    );
    producers
        .formulas
        .insert(upstream.clone(), OwnershipFormula::Unavailable);
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Failed(ProductFailure::NativeLowering)
    );
    assert!(
        !driver.session().memo.rooted[&packaging].changes.is_empty(),
        "failed prerequisites do not acknowledge delivered changes"
    );
    producers
        .formulas
        .insert(upstream, OwnershipFormula::Value(ProductValue::Unit));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(
        driver.session().memo.rooted[&packaging].changes.is_empty(),
        "accepted publication acknowledges its delivered changes"
    );
}

#[test]
fn a_rejected_root_completion_retains_its_delivered_changes() {
    let tel = ConfiguredTelemetry::new();
    let seed = ProductKey::RootBackendProduct(RootId::for_test(0));
    let packaging = ProductKey::RootBackendProduct(RootId::for_test(1));
    let types = fake_types();
    let mut driver = ProductDriver::new(&tel, RootId::for_test(189));
    {
        let mut session = driver.session_mut();
        assert!(finish_test_entry(
            &mut session.memo,
            &tel,
            &seed,
            ProductValue::Unit,
            ProductDependencies::default(),
            &types
        ));
        assert!(session.memo.begin(packaging.clone()));
        let mut context = ProductReadContext::new(&mut session);
        assert_eq!(
            context.read_rooted_products(&tel, packaging.clone(), seed.clone(), &types),
            Ok(vec![(seed.clone(), Some(ProductValue::Unit))])
        );
        let (dependencies, _) = context.into_completion();
        session.memo.invalidate_products(&tel, [packaging.clone()], &types);
        assert!(!finish_test_entry(
            &mut session.memo,
            &tel,
            &packaging,
            ProductValue::Unit,
            dependencies,
            &types
        ));
        assert_eq!(session.memo.rooted[&packaging].changes, HashSet::from([seed.clone()]));
    }
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types,
        calls: Vec::new(),
        formulas: HashMap::from([(packaging.clone(), OwnershipFormula::Root(seed))]),
    };
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(driver.session().memo.rooted[&packaging].changes.is_empty());
}

#[test]
fn an_equal_dirty_membership_chain_advances_once_per_owner() {
    assert_dirty_membership_chain_work(false, false, false);
}

#[test]
fn a_changed_membership_chain_head_does_not_restart_its_equal_tail() {
    assert_dirty_membership_chain_work(true, false, false);
}

#[test]
fn a_waiting_rooted_query_does_not_rescan_its_unchanged_control_prefix() {
    assert_dirty_membership_chain_work(false, true, false);
}

#[test]
fn equal_chain_owners_can_add_one_leaf_without_restarting_the_current_query() {
    assert_dirty_membership_chain_work(false, false, true);
}

#[test]
fn independent_rooted_owners_share_the_existing_prerequisite_batch() {
    assert_independent_rooted_prerequisite_batch(false);
}

#[test]
fn an_unobserved_membership_prerequisite_is_discovered_by_its_first_reader() {
    assert_independent_rooted_prerequisite_batch(true);
}

fn assert_independent_rooted_prerequisite_batch(distinct_parents: bool) {
    let tel = ConfiguredTelemetry::new();
    let evaluations = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&evaluations);
    tel.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
        PRODUCT_EVALUATED_EVENT,
        move |_, _, _, key, _, outcome| observed.borrow_mut().push((key.clone(), outcome.clone())),
    );
    let [seed, first, prerequisite, child, packaging] =
        [0, 1, 2, 3, 4].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        formulas: HashMap::from([
            (
                seed.clone(),
                OwnershipFormula::Seed(vec![first.clone(), prerequisite.clone()], ProductValue::Unit),
            ),
            (
                first.clone(),
                OwnershipFormula::Seed(vec![child.clone()], ProductValue::Unit),
            ),
            (prerequisite.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (child.clone(), OwnershipFormula::Copy(prerequisite.clone())),
            (packaging.clone(), OwnershipFormula::Root(seed.clone())),
        ]),
        calls: Vec::new(),
    };
    if distinct_parents {
        let owner = ProductKey::RootBackendProduct(RootId::for_test(5));
        producers.formulas.insert(
            seed,
            OwnershipFormula::Seed(vec![first, owner.clone()], ProductValue::Unit),
        );
        producers.formulas.insert(
            owner,
            OwnershipFormula::Seed(
                vec![ProductKey::RootBackendProduct(RootId::for_test(2))],
                ProductValue::Unit,
            ),
        );
    }
    let mut driver = ProductDriver::new(&tel, RootId::for_test(904));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        producers.calls.iter().filter(|key| *key == &child).count(),
        if distinct_parents { 2 } else { 1 },
        "an already exposed prerequisite is shared; an unobserved owner edge cannot order work before its first read"
    );
    let outcomes = evaluations
        .borrow()
        .iter()
        .filter(|(key, _)| key == &child)
        .map(|(_, outcome)| outcome.clone())
        .collect::<Vec<_>>();
    if distinct_parents {
        assert_eq!(
            outcomes,
            [
                PullOutcome::wait_on_product(prerequisite),
                PullOutcome::Produced(ProductValue::Unit)
            ],
            "the first actual observation discovers the prerequisite, followed by one dependency-triggered resumption"
        );
    } else {
        assert_eq!(outcomes, [PullOutcome::Produced(ProductValue::Unit)]);
    }
}

#[test]
fn newly_exposed_rooted_prerequisites_run_before_queued_later_owners() {
    assert_newly_exposed_prerequisite_order(false);
}

#[test]
fn equal_retained_owner_clearance_exposes_existing_children_before_queued_later_owners() {
    assert_newly_exposed_prerequisite_order(true);
}

fn assert_newly_exposed_prerequisite_order(retained: bool) {
    let tel = ConfiguredTelemetry::new();
    let [seed, first, child, reader, packaging] =
        [0, 1, 2, 3, 4].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        formulas: HashMap::from([
            (
                seed.clone(),
                OwnershipFormula::Seed(vec![first.clone(), reader.clone()], ProductValue::Unit),
            ),
            (
                first.clone(),
                OwnershipFormula::Seed(vec![child.clone()], ProductValue::Unit),
            ),
            (child.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (reader.clone(), OwnershipFormula::Copy(child.clone())),
            (packaging.clone(), OwnershipFormula::Root(seed)),
        ]),
        calls: Vec::new(),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(909));
    if retained {
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        driver.session_mut().memo.invalidate_products(
            &tel,
            [first, child, reader.clone(), packaging.clone()],
            &producers.types,
        );
        producers.calls.clear();
    }
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(
        producers.calls.iter().filter(|key| *key == &reader).count(),
        1,
        "a fixed older batch cannot hide its newly exposed earlier prerequisite"
    );
}

#[test]
fn an_alternate_parent_that_cleared_earlier_admits_the_reparented_branch() {
    let tel = ConfiguredTelemetry::new();
    let requests = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&requests);
    tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(PRODUCT_REQUESTED_EVENT, move |_, _, _, key, _| {
        observed.borrow_mut().push(key.clone())
    });
    let [seed, alternate, owner, child, packaging] =
        [0, 1, 2, 3, 4].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        formulas: HashMap::from([
            (
                seed.clone(),
                OwnershipFormula::Seed(vec![owner.clone()], ProductValue::Unit),
            ),
            (
                owner.clone(),
                OwnershipFormula::Seed(vec![child.clone()], ProductValue::Unit),
            ),
            (
                alternate.clone(),
                OwnershipFormula::Seed(vec![child.clone()], ProductValue::Unit),
            ),
            (child.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (packaging.clone(), OwnershipFormula::Root(seed.clone())),
        ]),
        calls: Vec::new(),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(910));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    producers.formulas.insert(
        seed.clone(),
        OwnershipFormula::Seed(vec![owner.clone(), alternate.clone()], ProductValue::Unit),
    );
    driver
        .session_mut()
        .memo
        .invalidate_products(&tel, [seed], &producers.types);
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    driver.session_mut().memo.invalidate_products(
        &tel,
        [owner.clone(), alternate, child.clone(), packaging.clone()],
        &producers.types,
    );
    producers
        .formulas
        .insert(owner, OwnershipFormula::Seed(Vec::new(), ProductValue::Unit));
    producers.calls.clear();
    requests.borrow_mut().clear();
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert_eq!(producers.calls.iter().filter(|key| *key == &child).count(), 1);
    assert_eq!(
        requests.borrow().iter().filter(|key| *key == &packaging).count(),
        2,
        "the exact reparent transition must admit the child to the still-live frame, without rediscovering the query"
    );
}

#[test]
fn restoring_an_interior_witness_entrance_admits_its_dirty_branch_before_queued_readers() {
    let tel = ConfiguredTelemetry::new();
    let requests = Rc::new(RefCell::new(Vec::new()));
    let recorded = Rc::clone(&requests);
    tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(PRODUCT_REQUESTED_EVENT, move |_, _, _, key, _| {
        recorded.borrow_mut().push(key.clone())
    });
    let [seed, owner, alternate, child, reader, detached, packaging] =
        [0, 1, 2, 3, 4, 5, 6].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        calls: Vec::new(),
        formulas: HashMap::from([
            (
                seed.clone(),
                OwnershipFormula::Seed(vec![owner.clone()], ProductValue::Unit),
            ),
            (
                owner.clone(),
                OwnershipFormula::Seed(vec![detached.clone()], ProductValue::Unit),
            ),
            (
                detached.clone(),
                OwnershipFormula::Seed(vec![child.clone()], ProductValue::Unit),
            ),
            (
                alternate.clone(),
                OwnershipFormula::Seed(vec![child.clone()], ProductValue::Unit),
            ),
            (child.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (reader.clone(), OwnershipFormula::Copy(child.clone())),
            (packaging.clone(), OwnershipFormula::Root(seed.clone())),
        ]),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(915));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    producers.formulas.insert(
        seed.clone(),
        OwnershipFormula::Seed(vec![owner.clone(), alternate, reader.clone()], ProductValue::Unit),
    );
    driver
        .session_mut()
        .memo
        .invalidate_products(&tel, [seed], &producers.types);
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    driver.session_mut().memo.invalidate_products(
        &tel,
        [
            owner.clone(),
            detached.clone(),
            child.clone(),
            reader.clone(),
            packaging.clone(),
        ],
        &producers.types,
    );
    producers
        .formulas
        .insert(owner, OwnershipFormula::Seed(Vec::new(), ProductValue::Unit));
    producers
        .formulas
        .insert(detached.clone(), OwnershipFormula::Unavailable);
    producers.calls.clear();
    requests.borrow_mut().clear();
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(
        !requests.borrow().contains(&detached),
        "the severed outer branch is obsolete"
    );
    assert_eq!(
        producers.calls.iter().filter(|key| *key == &reader).count(),
        1,
        "a restored interior entrance exposes its still-needed earlier prerequisite before queued readers"
    );
    assert_eq!(producers.calls.iter().filter(|key| *key == &child).count(), 1);
    assert_eq!(requests.borrow().iter().filter(|key| *key == &packaging).count(), 2);
}

#[test]
fn reparent_admission_reuses_the_unchanged_common_witness_prefix() {
    let mut repeated_prefixes = Vec::new();
    for (size, candidate_depth, candidate_count, alternating) in [8_u32, 32, 64].into_iter().flat_map(|size| {
        [
            (size, 0, 1, false),
            (size, size, 1, false),
            (size, size, 2, false),
            (size, size, 2, true),
        ]
    }) {
        let tel = ConfiguredTelemetry::new();
        let visits = Rc::new(Cell::new(0));
        let observed = Rc::clone(&visits);
        let repairs = Rc::new(RefCell::new(Vec::new()));
        let recorded = Rc::clone(&repairs);
        tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
            &["fz", "compiler2", "pull", "product", "validation"],
            move |_, _, _, owner, work| {
                observed.set(observed.get() + work.witness_visits);
                if work.reparent_candidates != 0 || work.reparent_proof_nodes != 0 {
                    recorded.borrow_mut().push((owner.clone(), *work));
                }
            },
        );
        let key = |id| ProductKey::RootBackendProduct(RootId::for_test(id));
        let prefix = (0..=size).map(key).collect::<Vec<_>>();
        let owners = (size + 1..size * 2 + 1).map(key).collect::<Vec<_>>();
        let children = (size * 2 + 1..size * 3 + 1).map(key).collect::<Vec<_>>();
        let candidate_paths = (0..candidate_count)
            .map(|candidate| {
                let first = size * 3 + 1 + candidate * (candidate_depth + 1);
                (first..first + candidate_depth + 1).map(key).collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let alternates = candidate_paths
            .iter()
            .map(|path| path.last().unwrap().clone())
            .collect::<HashSet<_>>();
        let packaging_id = size * 3 + 1 + candidate_count * (candidate_depth + 1);
        let packaging = key(packaging_id);
        let mut formulas = HashMap::new();
        for (index, member) in prefix.iter().enumerate() {
            let next = prefix
                .get(index + 1)
                .cloned()
                .map(|key| vec![key])
                .unwrap_or_else(|| owners.clone());
            formulas.insert(member.clone(), OwnershipFormula::Seed(next, ProductValue::Unit));
        }
        for (owner, child) in owners.iter().zip(&children) {
            formulas.insert(
                owner.clone(),
                OwnershipFormula::Seed(vec![child.clone()], ProductValue::Unit),
            );
            formulas.insert(child.clone(), OwnershipFormula::Value(ProductValue::Unit));
        }
        for (candidate, path) in candidate_paths.iter().enumerate() {
            for (index, member) in path.iter().enumerate() {
                let next = path.get(index + 1).cloned().map(|key| vec![key]).unwrap_or_else(|| {
                    children
                        .iter()
                        .enumerate()
                        .filter(|(index, _)| !alternating || index % candidate_count as usize == candidate)
                        .map(|(_, child)| child.clone())
                        .collect()
                });
                formulas.insert(member.clone(), OwnershipFormula::Seed(next, ProductValue::Unit));
            }
        }
        formulas.insert(packaging.clone(), OwnershipFormula::Root(prefix[0].clone()));
        let mut producers = OwnershipProducers {
            telemetry: &tel,
            types: fake_types(),
            formulas,
            calls: Vec::new(),
        };
        let mut driver = ProductDriver::new(&tel, RootId::for_test(911));
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        let mut next = owners.clone();
        next.extend(candidate_paths.iter().map(|path| path[0].clone()));
        producers.formulas.insert(
            prefix[size as usize].clone(),
            OwnershipFormula::Seed(next, ProductValue::Unit),
        );
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [prefix[size as usize].clone()], &producers.types);
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        let retained = prefix
            .iter()
            .chain(candidate_paths.iter().flatten())
            .map(|key| {
                (
                    key.clone(),
                    driver.session().memo.produced[key].generation,
                    Rc::clone(&driver.session().memo.produced[key].dependencies),
                )
            })
            .collect::<Vec<_>>();
        repairs.borrow_mut().clear();
        visits.set(0);
        driver.session_mut().memo.invalidate_products(
            &tel,
            owners
                .iter()
                .chain(&children)
                .chain(std::iter::once(&packaging))
                .cloned(),
            &producers.types,
        );
        for owner in &owners {
            producers
                .formulas
                .insert(owner.clone(), OwnershipFormula::Seed(Vec::new(), ProductValue::Unit));
        }
        producers.calls.clear();
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        let admission_visits = visits.get();
        if candidate_depth == 0 && candidate_count == 1 {
            assert!(
                admission_visits <= u64::from(size) * 8 + 8,
                "admitting sibling reparent branches must not rescan their unchanged common prefix: {admission_visits}",
            );
        }
        for key in owners.iter().chain(&children) {
            assert_eq!(producers.calls.iter().filter(|called| *called == key).count(), 1);
            assert_eq!(
                driver.session().memo.generation(key),
                Some(1),
                "equal reproduction keeps its generation"
            );
        }
        for (key, generation, dependencies) in &retained {
            let session = driver.session();
            let entry = &session.memo.produced[key];
            assert_eq!(entry.generation, *generation);
            assert!(Rc::ptr_eq(&entry.dependencies, dependencies));
            assert!(
                !producers.calls.contains(key),
                "the unchanged prefix and alternate are retained"
            );
        }
        for owner in &owners {
            assert!(driver.session().memo.produced[owner].membership.is_empty());
        }
        for (index, child) in children.iter().enumerate() {
            let expected = if alternating {
                HashSet::from([candidate_paths[index % candidate_count as usize]
                    .last()
                    .unwrap()
                    .clone()])
            } else {
                alternates.clone()
            };
            assert_eq!(driver.session().memo.membership_readers[child], expected);
            assert!(driver.session().memo.rooted_readers[child].contains(&packaging));
        }
        let repair = repairs
            .borrow()
            .iter()
            .fold(ProductValidation::default(), |mut total, (_, work)| {
                total.include(*work);
                total
            });
        let candidates_per_child = if alternating { 1 } else { candidate_count };
        assert_eq!(repair.reparent_candidates, u64::from(size * candidates_per_child));
        assert_eq!(
            repairs.borrow().len(),
            size as usize,
            "the repeated prefix spans separate committed owners"
        );
        assert_eq!(
            repairs
                .borrow()
                .iter()
                .map(|(owner, _)| owner.clone())
                .collect::<HashSet<_>>(),
            owners.iter().cloned().collect()
        );
        repairs.borrow_mut().clear();
        visits.set(0);
        producers.calls.clear();
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert!(producers.calls.is_empty());
        assert!(repairs.borrow().is_empty());
        assert_eq!(visits.get(), 0);
        let unrelated = key(packaging_id + 1);
        producers
            .formulas
            .insert(unrelated.clone(), OwnershipFormula::Value(ProductValue::Unit));
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &unrelated),
            PullOutcome::Produced(ProductValue::Unit)
        );
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [unrelated], &producers.types);
        producers.calls.clear();
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert!(producers.calls.is_empty());
        assert!(repairs.borrow().is_empty());
        assert_eq!(visits.get(), 0);
        let bound = u64::from(size);
        if repair.reparent_proof_nodes != bound {
            repeated_prefixes.push(format!("D=K={size}, candidate_depth={candidate_depth}, candidate_count={candidate_count}, alternating={alternating}, admission_visits={admission_visits}, candidates={}, proof_nodes={}, bound={bound}", repair.reparent_candidates, repair.reparent_proof_nodes));
        }
    }
    assert!(
        repeated_prefixes.is_empty(),
        "alternate repair must stop before rescanning the clean common prefix:\n{}",
        repeated_prefixes.join("\n")
    );
}

#[test]
fn queued_rooted_owners_cannot_outlive_a_fact_change_to_their_witness() {
    for reenter_formula in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let [seed, first, obsolete, packaging] =
            [0, 1, 2, 3].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
        let fact = FactKey::RootEntry(RootId::for_test(905));
        let mut producers = OwnershipProducers {
            telemetry: &tel,
            types: fake_types(),
            formulas: HashMap::from([
                (
                    seed.clone(),
                    OwnershipFormula::FactMembership {
                        fact: fact.clone(),
                        state: FactState {
                            revision: Some(1),
                            settled: true,
                        },
                        children: vec![first.clone(), obsolete.clone()],
                    },
                ),
                (first.clone(), OwnershipFormula::Value(ProductValue::Unit)),
                (obsolete.clone(), OwnershipFormula::Value(ProductValue::Unit)),
                (packaging.clone(), OwnershipFormula::Root(seed.clone())),
            ]),
            calls: Vec::new(),
        };
        let mut driver = ProductDriver::new(&tel, RootId::for_test(905));
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [first.clone(), obsolete.clone()], &producers.types);
        if reenter_formula {
            driver
                .session_mut()
                .memo
                .invalidate_products(&tel, [packaging.clone()], &producers.types);
        }
        producers.formulas.insert(
            first.clone(),
            OwnershipFormula::DeliverMembershipFact {
                fact,
                owner: seed,
                children: vec![first],
            },
        );
        producers
            .formulas
            .insert(obsolete.clone(), OwnershipFormula::Unavailable);
        producers.calls.clear();
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit),
            "reenter_formula={reenter_formula}"
        );
        assert!(
            !producers.calls.contains(&obsolete),
            "queued demand must be revoked when its current witness owner changes"
        );
    }
}

#[test]
fn canceling_an_outer_rooted_query_discards_nested_waits_but_keeps_live_siblings() {
    let tel = ConfiguredTelemetry::new();
    let requests = Rc::new(RefCell::new(Vec::new()));
    let recorded = Rc::clone(&requests);
    tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(PRODUCT_REQUESTED_EVENT, move |_, _, _, key, _| {
        recorded.borrow_mut().push(key.clone())
    });
    let [seed, nested, sibling, nested_seed, first, obsolete, packaging] =
        [0, 1, 2, 3, 4, 5, 6].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let fact = FactKey::RootEntry(RootId::for_test(906));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        formulas: HashMap::from([
            (
                seed.clone(),
                OwnershipFormula::FactMembership {
                    fact: fact.clone(),
                    state: FactState {
                        revision: Some(1),
                        settled: true,
                    },
                    children: vec![nested.clone(), sibling.clone()],
                },
            ),
            (nested.clone(), OwnershipFormula::Root(nested_seed.clone())),
            (
                nested_seed,
                OwnershipFormula::Seed(vec![first.clone(), obsolete.clone()], ProductValue::Unit),
            ),
            (first.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (obsolete.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (sibling.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (packaging.clone(), OwnershipFormula::Root(seed.clone())),
        ]),
        calls: Vec::new(),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(906));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    driver.session_mut().memo.invalidate_products(
        &tel,
        [
            nested,
            sibling.clone(),
            first.clone(),
            obsolete.clone(),
            packaging.clone(),
        ],
        &producers.types,
    );
    producers.formulas.insert(
        first,
        OwnershipFormula::DeliverMembershipFact {
            fact,
            owner: seed,
            children: vec![sibling.clone()],
        },
    );
    producers
        .formulas
        .insert(obsolete.clone(), OwnershipFormula::Unavailable);
    producers.calls.clear();
    requests.borrow_mut().clear();
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(
        !requests.borrow().contains(&obsolete),
        "outer demand revocation precedes even nested requested telemetry"
    );
    assert_eq!(
        producers.calls.iter().filter(|key| *key == &sibling).count(),
        1,
        "the new owner still demands its live sibling"
    );
}

#[test]
fn canceling_a_nested_query_keeps_its_still_demanded_parent_admission() {
    let tel = ConfiguredTelemetry::new();
    let requests = Rc::new(RefCell::new(Vec::new()));
    let recorded = Rc::clone(&requests);
    tel.attach_raw_event2::<ProductKey, ProductRequestId, _>(PRODUCT_REQUESTED_EVENT, move |_, _, _, key, _| {
        recorded.borrow_mut().push(key.clone())
    });
    let [seed, owner, child, reader, inner_seed, delivery, obsolete, packaging] =
        [0, 1, 2, 3, 4, 5, 6, 7].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let fact = FactKey::RootEntry(RootId::for_test(912));
    let before = FactState {
        revision: Some(1),
        settled: true,
    };
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        calls: Vec::new(),
        formulas: HashMap::from([
            (
                seed.clone(),
                OwnershipFormula::Seed(vec![owner.clone(), reader.clone()], ProductValue::Unit),
            ),
            (
                owner.clone(),
                OwnershipFormula::FactMembership {
                    fact: fact.clone(),
                    state: before,
                    children: Vec::new(),
                },
            ),
            (reader.clone(), OwnershipFormula::Copy(child.clone())),
            (child.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (packaging.clone(), OwnershipFormula::Root(seed)),
            (
                inner_seed.clone(),
                OwnershipFormula::Seed(vec![delivery.clone(), obsolete.clone()], ProductValue::Unit),
            ),
            (
                delivery,
                OwnershipFormula::DeliverMembershipFact {
                    fact: fact.clone(),
                    owner: owner.clone(),
                    children: vec![child.clone()],
                },
            ),
            (obsolete.clone(), OwnershipFormula::Unavailable),
        ]),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(912));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    driver.session_mut().memo.invalidate_products(
        &tel,
        [owner.clone(), reader.clone(), child.clone(), packaging.clone()],
        &producers.types,
    );
    producers.formulas.insert(
        owner,
        OwnershipFormula::FactRoot {
            fact,
            state: before,
            seed: inner_seed,
        },
    );
    producers.calls.clear();
    requests.borrow_mut().clear();
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(
        !requests.borrow().contains(&obsolete),
        "the canceled nested sibling is never requested"
    );
    assert_eq!(
        producers.calls.iter().filter(|key| *key == &reader).count(),
        1,
        "retrying the still-demanded owner must expose its earlier child to the surviving frame"
    );
    assert_eq!(producers.calls.iter().filter(|key| *key == &child).count(), 1);
    assert_eq!(requests.borrow().iter().filter(|key| *key == &packaging).count(), 2);
}

#[test]
fn wait_frames_belong_to_the_actual_pending_attempt_and_keep_its_oldest_registration() {
    let tel = ConfiguredTelemetry::new();
    let [seed, child, packaging] = [0, 1, 2].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        formulas: HashMap::from([
            (
                seed.clone(),
                OwnershipFormula::Seed(vec![child.clone()], ProductValue::Unit),
            ),
            (child, OwnershipFormula::Value(ProductValue::Unit)),
            (packaging.clone(), OwnershipFormula::Root(seed.clone())),
        ]),
        calls: Vec::new(),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(907));
    assert!(matches!(driver.pull(&mut producers, seed), PullOutcome::Produced(_)));
    assert!(matches!(
        driver.pull(&mut producers, packaging.clone()),
        PullOutcome::Waiting(_)
    ));
    let first = driver.register_wait_frame(&packaging, 0).unwrap();
    assert!(matches!(
        driver.pull(&mut producers, packaging.clone()),
        PullOutcome::Waiting(_)
    ));
    assert_eq!(
        driver.register_wait_frame(&packaging, 3),
        Some(first),
        "continuation pulls do not replace the actual observation identity"
    );
    driver.unregister_wait_frame(&packaging, first, 3);
    driver
        .session_mut()
        .memo
        .invalidate_products(&tel, [packaging.clone()], &producers.types);
    assert_eq!(
        driver.reconcile_wait_frames(&producers.types),
        Some((0, first)),
        "inner unregister cannot detach the older owner"
    );
    assert!(matches!(
        driver.pull(&mut producers, packaging.clone()),
        PullOutcome::Waiting(_)
    ));
    let replacement = driver.register_wait_frame(&packaging, 0).unwrap();
    assert_ne!(
        replacement, first,
        "equal-shaped observations still belong to different actual evaluations"
    );
    driver.unregister_wait_frame(&packaging, first, 0);
    driver.session_mut().memo.abort(&packaging);
    assert_eq!(
        driver.reconcile_wait_frames(&producers.types),
        Some((0, replacement)),
        "a retired frame cannot unregister the replacement at its old slot"
    );
    assert_eq!(driver.reconcile_wait_frames(&producers.types), None);
}

#[test]
fn failed_rooted_drives_unregister_their_frames_before_retained_repair() {
    let tel = ConfiguredTelemetry::new();
    let [seed, child, sibling, packaging] = [0, 1, 2, 3].map(|id| ProductKey::RootBackendProduct(RootId::for_test(id)));
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        formulas: HashMap::from([
            (
                seed.clone(),
                OwnershipFormula::Seed(vec![child.clone(), sibling.clone()], ProductValue::Unit),
            ),
            (child.clone(), OwnershipFormula::Unavailable),
            (sibling.clone(), OwnershipFormula::Unavailable),
            (packaging.clone(), OwnershipFormula::Root(seed)),
        ]),
        calls: Vec::new(),
    };
    let mut driver = ProductDriver::new(&tel, RootId::for_test(908));
    assert!(matches!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Failed(_)
    ));
    assert!(
        driver
            .session()
            .memo
            .pending_dependencies
            .values()
            .all(|pending| pending.waiting_frame.is_none())
    );
    assert!(driver.session().memo.canceled_wait_frame.is_none());
    assert!(driver.session().memo.wait_frame_exposures.is_empty());
    let origin = driver.session().memo.pending_dependencies[&packaging].request;
    producers
        .formulas
        .insert(child, OwnershipFormula::Value(ProductValue::Unit));
    assert!(matches!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Failed(_)
    ));
    assert_eq!(
        driver.session().memo.pending_dependencies[&packaging].request,
        origin,
        "the same actual observation survives retry; teardown cannot depend on a fresh attempt identity"
    );
    assert!(driver.session().memo.wait_frame_exposures.is_empty());
    producers
        .formulas
        .insert(sibling, OwnershipFormula::Value(ProductValue::Unit));
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    assert!(
        driver
            .session()
            .memo
            .pending_dependencies
            .values()
            .all(|pending| pending.waiting_frame.is_none())
    );
    assert!(driver.session().memo.canceled_wait_frame.is_none());
}

#[test]
fn an_equal_dirty_cycle_prefix_is_validated_once_before_a_missing_membership_chain() {
    for size in [8_u32, 32, 64] {
        let tel = ConfiguredTelemetry::new();
        let edges = Rc::new(Cell::new(0));
        let observed = Rc::clone(&edges);
        tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
            &["fz", "compiler2", "pull", "product", "validation"],
            move |_, _, _, _, work| observed.set(observed.get() + work.edge_scans),
        );
        let key = |id| ProductKey::RootBackendProduct(RootId::for_test(id));
        let [selector, left, right, packaging] = [1000, 1001, 1002, 1003].map(key);
        let chain = (0..size).map(key).collect::<Vec<_>>();
        let mut formulas = chain
            .iter()
            .enumerate()
            .map(|(index, member)| {
                (
                    member.clone(),
                    OwnershipFormula::Seed(chain.get(index + 1).cloned().into_iter().collect(), ProductValue::Unit),
                )
            })
            .collect::<HashMap<_, _>>();
        formulas.extend([
            (selector.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (left.clone(), OwnershipFormula::Unavailable),
            (right.clone(), OwnershipFormula::Unavailable),
            (packaging.clone(), OwnershipFormula::Root(left.clone())),
        ]);
        let mut producers = OwnershipProducers {
            telemetry: &tel,
            types: fake_types(),
            formulas,
            calls: Vec::new(),
        };
        let mut driver = ProductDriver::new(&tel, RootId::for_test(192));
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &selector),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert!(finish_test_group(
            &mut driver.session_mut().memo,
            &tel,
            &left,
            vec![
                (
                    left.clone(),
                    ProductValue::Unit,
                    ProductDependencies {
                        products: IndexMap::from([(selector.clone(), Some(1)), (right.clone(), None)]),
                        membership: HashSet::from([chain[0].clone()]),
                        ..ProductDependencies::default()
                    }
                ),
                (
                    right.clone(),
                    ProductValue::Unit,
                    ProductDependencies {
                        products: IndexMap::from([(selector.clone(), Some(1)), (left.clone(), None)]),
                        ..ProductDependencies::default()
                    }
                ),
            ],
            &producers.types
        ));
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [selector.clone()], &producers.types);
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &selector),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert!(driver.session().memo.dirty_descendants.contains(&left));
        assert!(driver.session().memo.dirty_descendants.contains(&right));
        driver.session_mut().memo.invalidate_products(
            &tel,
            chain.iter().cloned().chain([packaging.clone()]),
            &producers.types,
        );
        edges.set(0);
        producers.calls.clear();
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert!(
            edges.get() <= 8,
            "one independent cycle proof must survive later member waits: size={size}, edge_scans={}",
            edges.get()
        );
        assert!(!producers.calls.contains(&left) && !producers.calls.contains(&right));
    }
}

#[test]
fn sibling_value_backedges_share_one_complete_rooted_proof() {
    for missing in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let key = |id| ProductKey::RootBackendProduct(RootId::for_test(id));
        let [selector, seed, left, right, child, packaging] = [0, 1, 2, 3, 4, 5].map(key);
        let mut producers = OwnershipProducers {
            telemetry: &tel,
            types: fake_types(),
            calls: Vec::new(),
            formulas: HashMap::from([
                (selector.clone(), OwnershipFormula::Value(ProductValue::Unit)),
                (seed.clone(), OwnershipFormula::Unavailable),
                (left.clone(), OwnershipFormula::Unavailable),
                (right.clone(), OwnershipFormula::Unavailable),
                (child.clone(), OwnershipFormula::Value(ProductValue::Unit)),
                (packaging.clone(), OwnershipFormula::Root(seed.clone())),
            ]),
        };
        let mut driver = ProductDriver::new(&tel, RootId::for_test(193));
        {
            let mut session = driver.session_mut();
            for product in [&selector, &packaging, &child] {
                assert!(finish_test_entry(
                    &mut session.memo,
                    &tel,
                    product,
                    ProductValue::Unit,
                    ProductDependencies::default(),
                    &producers.types
                ));
            }
            assert!(finish_test_entry(
                &mut session.memo,
                &tel,
                &left,
                ProductValue::Unit,
                ProductDependencies {
                    products: IndexMap::from([(selector.clone(), Some(1)), (packaging.clone(), Some(1))]),
                    ..ProductDependencies::default()
                },
                &producers.types
            ));
            assert!(finish_test_entry(
                &mut session.memo,
                &tel,
                &right,
                ProductValue::Unit,
                ProductDependencies {
                    products: IndexMap::from([(packaging.clone(), Some(1))]),
                    ..ProductDependencies::default()
                },
                &producers.types
            ));
            assert!(finish_test_entry(
                &mut session.memo,
                &tel,
                &seed,
                ProductValue::Unit,
                ProductDependencies {
                    membership: [left.clone(), right.clone()]
                        .into_iter()
                        .chain(missing.then(|| child.clone()))
                        .collect(),
                    ..ProductDependencies::default()
                },
                &producers.types
            ));
            session.memo.register_rooted(packaging.clone(), seed, &producers.types);
            Rc::get_mut(&mut session.memo.produced.get_mut(&packaging).unwrap().dependencies)
                .unwrap()
                .rooted_read = Some(RootedRead {
                position: 0,
                delivered: true,
                controls_delivered: true,
            });
            let rooted = session.memo.rooted.get_mut(&packaging).unwrap();
            rooted.dirty.clear();
            rooted.changes.clear();
            session
                .memo
                .invalidate_products(&tel, [selector.clone()], &producers.types);
        }
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &selector),
            PullOutcome::Produced(ProductValue::Unit)
        );
        producers.calls.clear();
        if missing {
            producers.formulas.insert(child.clone(), OwnershipFormula::Unavailable);
            driver
                .session_mut()
                .memo
                .invalidate_products(&tel, [child.clone()], &producers.types);
            assert_eq!(
                ownership_pull(&mut driver, &mut producers, &packaging),
                PullOutcome::Failed(ProductFailure::NativeLowering)
            );
            assert!(
                driver.session().memo.dirty_descendants.contains(&left),
                "failed full proof cannot clear one backedge provisionally"
            );
            producers
                .formulas
                .insert(child, OwnershipFormula::Value(ProductValue::Unit));
        }
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &packaging),
            PullOutcome::Produced(ProductValue::Unit)
        );
        assert!(!producers.calls.contains(&left) && !producers.calls.contains(&right));
        assert!(driver.session().memo.rooted[&packaging].dirty.is_empty());
        for product in [&packaging, &left, &right] {
            assert_eq!(driver.session().memo.generation(product), Some(1));
        }
    }
}

fn assert_dirty_membership_chain_work(changed_head: bool, with_prefix: bool, adds_leaf: bool) {
    for size in [8_u32, 32, 64] {
        for order in 0..3 {
            let tel = ConfiguredTelemetry::new();
            let visits = Rc::new(Cell::new(0));
            let edges = Rc::new(Cell::new(0));
            let maintenance = Rc::new(Cell::new(0));
            let comparisons = Rc::new(Cell::new(0));
            let observed_comparisons = Rc::clone(&comparisons);
            let observed_maintenance = Rc::clone(&maintenance);
            let observed_edges = Rc::clone(&edges);
            let observed = Rc::clone(&visits);
            tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
                &["fz", "compiler2", "pull", "product", "validation"],
                move |_, _, _, _, work| {
                    observed.set(observed.get() + work.witness_visits);
                    observed_edges.set(observed_edges.get() + work.edge_scans);
                    observed_maintenance.set(observed_maintenance.get() + work.witness_updates + work.cursor_rewinds);
                    observed_comparisons.set(observed_comparisons.get() + work.ordering_comparisons);
                },
            );
            let root = RootId::for_test(185);
            let key = |id| ProductKey::RootBackendProduct(RootId::for_test(id));
            let packaging = key(1000);
            let members = (0..size).map(key).collect::<Vec<_>>();
            let mut formulas = members
                .iter()
                .enumerate()
                .map(|(index, member)| {
                    (
                        member.clone(),
                        OwnershipFormula::Seed(
                            members.get(index + 1).cloned().into_iter().collect(),
                            ProductValue::Unit,
                        ),
                    )
                })
                .collect::<HashMap<_, _>>();
            if with_prefix {
                let prefix = (2000..2000 + size).map(key).collect::<Vec<_>>();
                for control in &prefix {
                    formulas.insert(control.clone(), OwnershipFormula::Value(ProductValue::Unit));
                }
                formulas.insert(
                    packaging.clone(),
                    OwnershipFormula::PrefixRoot(prefix, members[0].clone()),
                );
            } else {
                formulas.insert(packaging.clone(), OwnershipFormula::Root(members[0].clone()));
            }
            let mut producers = OwnershipProducers {
                telemetry: &tel,
                types: fake_types(),
                formulas,
                calls: Vec::new(),
            };
            let mut driver = ProductDriver::new(&tel, root);
            assert_eq!(
                ownership_pull(&mut driver, &mut producers, &packaging),
                PullOutcome::Produced(ProductValue::Unit)
            );
            visits.set(0);
            edges.set(0);
            maintenance.set(0);
            comparisons.set(0);
            producers.calls.clear();
            if adds_leaf {
                for (index, member) in members.iter().enumerate() {
                    let leaf = key(2000 + index as u32);
                    let children = members
                        .get(index + 1)
                        .cloned()
                        .into_iter()
                        .chain([leaf.clone()])
                        .collect();
                    producers
                        .formulas
                        .insert(member.clone(), OwnershipFormula::Seed(children, ProductValue::Unit));
                    producers
                        .formulas
                        .insert(leaf, OwnershipFormula::Value(ProductValue::Unit));
                }
            }
            if changed_head {
                producers.formulas.insert(
                    members[0].clone(),
                    OwnershipFormula::Seed(vec![members[1].clone()], ownership_selected(true)),
                );
            }
            let mut invalidated = (0..size).collect::<Vec<_>>();
            match order {
                0 => {}
                1 => invalidated.reverse(),
                _ => invalidated.sort_by_key(|index| (index * 13) % size),
            }
            driver.session_mut().memo.invalidate_products(
                &tel,
                invalidated
                    .into_iter()
                    .map(|index| members[index as usize].clone())
                    .chain([packaging.clone()]),
                &producers.types,
            );
            assert_eq!(
                ownership_pull(&mut driver, &mut producers, &packaging),
                PullOutcome::Produced(ProductValue::Unit)
            );
            let packaging_evaluations = producers.calls.iter().filter(|key| *key == &packaging).count();
            let changed_members = u64::from(size) * if adds_leaf { 2 } else { 1 };
            assert!(
                comparisons.get() <= changed_members * u64::from(size.ilog2() + 2) * 4,
                "interleaved admission and selection stay n log n across the whole drive: {}",
                comparisons.get()
            );
            assert!(
                maintenance.get() <= changed_members * 12,
                "whole request includes marking, cursor repair and pruning across all mutation events: size={size}, order={order}, work={}",
                maintenance.get()
            );
            if with_prefix {
                assert_eq!(
                    edges.get(),
                    0,
                    "a live waiting query must not rescan its unchanged ordinary prefix; size={size}"
                );
                assert_eq!(packaging_evaluations, 2);
                continue;
            }
            assert!(
                visits.get() <= changed_members * 3,
                "a whole chain request must advance through ownership once: size={size}, order={order}, changed_head={changed_head}, witness_visits={}, packaging_evaluations={packaging_evaluations}",
                visits.get()
            );
            assert!(
                packaging_evaluations <= 2,
                "packaging must wait for its owned chain without restarting for every owner"
            );
        }
    }
}

#[test]
fn a_failed_shared_control_validation_cannot_authorize_sibling_membership() {
    let tel = ConfiguredTelemetry::new();
    let root = RootId::for_test(184);
    let key = |id| ProductKey::RootBackendProduct(RootId::for_test(id));
    let first = key(0);
    let old_child = key(1);
    let second = key(2);
    let seed = key(3);
    let selector = key(4);
    let upstream = key(5);
    let packaging = key(6);
    let mut producers = OwnershipProducers {
        telemetry: &tel,
        types: fake_types(),
        calls: Vec::new(),
        formulas: HashMap::from([
            (first.clone(), OwnershipFormula::Copy(selector.clone())),
            (
                second.clone(),
                OwnershipFormula::Membership {
                    selector: selector.clone(),
                    child: old_child.clone(),
                },
            ),
            (
                seed.clone(),
                OwnershipFormula::Seed(vec![first, second], ProductValue::Unit),
            ),
            (selector, OwnershipFormula::Copy(upstream.clone())),
            (upstream.clone(), OwnershipFormula::Value(ownership_selected(true))),
            (old_child.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            (packaging.clone(), OwnershipFormula::Root(seed)),
        ]),
    };
    let mut driver = ProductDriver::new(&tel, root);
    assert_eq!(
        ownership_pull(&mut driver, &mut producers, &packaging),
        PullOutcome::Produced(ProductValue::Unit)
    );
    producers.calls.clear();
    producers
        .formulas
        .insert(upstream.clone(), OwnershipFormula::Value(ownership_selected(false)));
    producers
        .formulas
        .insert(old_child.clone(), OwnershipFormula::Unavailable);
    driver.session_mut().memo.invalidate_products(
        &tel,
        [upstream, old_child.clone(), packaging.clone()],
        &producers.types,
    );
    let outcome = ownership_pull(&mut driver, &mut producers, &packaging);
    assert!(
        !producers.calls.contains(&old_child),
        "a failed sibling validation must not authorize an obsolete membership child: {:?}",
        producers.calls
    );
    assert_eq!(outcome, PullOutcome::Produced(ProductValue::Unit));
}

#[test]
fn equal_recursive_validation_visits_shared_inputs_once_and_only_mutates_its_external_reader() {
    for size in [8, 64, 256] {
        let tel = ConfiguredTelemetry::new();
        let work = Rc::new(RefCell::new(Vec::new()));
        let observed = Rc::clone(&work);
        tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
            &["fz", "compiler2", "pull", "product", "validation"],
            move |_, _, _, _, validation| observed.borrow_mut().push(*validation),
        );
        let root = RootId::for_test(183);
        let key = |id| ProductKey::ExecutableEffects(fake_executable_with_function(root, id));
        let members = (0..size).map(key).collect::<Vec<_>>();
        let input = key(size);
        let reader = key(size + 1);
        let types = fake_types();
        let mut memo = ProductMemo::default();
        finish_test_product(&mut memo, &input, ProductValue::Unit, []);
        let entries = members
            .iter()
            .enumerate()
            .map(|(index, member)| {
                (
                    member.clone(),
                    ProductValue::Unit,
                    ProductDependencies {
                        products: [
                            (members[(index + 1) % members.len()].clone(), None),
                            (input.clone(), Some(1)),
                        ]
                        .into_iter()
                        .collect(),
                        ..ProductDependencies::default()
                    },
                )
            })
            .collect();
        assert!(finish_test_group(&mut memo, &tel, &members[0], entries, &types));
        finish_test_product(&mut memo, &reader, ProductValue::Unit, [members[0].clone()]);
        memo.invalidate_products(&tel, [input.clone()], &types);
        finish_test_product(&mut memo, &input, ProductValue::Unit, []);
        work.borrow_mut().clear();
        assert_eq!(memo.stale_dependency(&tel, &members[0], &types), None);
        let mut validation = ProductValidation::default();
        for work in work.borrow().iter() {
            validation.include(*work);
        }
        assert_eq!(
            validation,
            ProductValidation {
                vertex_visits: u64::from(size),
                edge_scans: u64::from(size) * 2,
                witness_visits: 0,
                witness_updates: 0,
                cursor_rewinds: 0,
                mutation_admissions: 1,
                mutation_pops: 1,
                mutation_edges: 1,
                reparent_candidates: 0,
                reparent_proof_nodes: 0,
                ordering_comparisons: 0,
            },
            "validation checks each internal edge once and refreshes only the one external reader"
        );
        assert!(memo.dirty_descendants.is_empty());
        for member in members.iter().chain([&reader]) {
            assert_eq!(memo.generation(member), Some(1));
        }
        work.borrow_mut().clear();
        assert_eq!(memo.stale_dependency(&tel, &members[0], &types), None);
        assert!(
            work.borrow().is_empty(),
            "a validated cycle does no further validation work"
        );
    }
}

#[test]
fn a_pending_formula_replaces_its_previous_attempts_observations() {
    let root = RootId::for_test(182);
    let reader = ProductKey::ExecutableEffects(fake_executable_with_function(root, 1820));
    let old = ProductKey::ExecutableEffects(fake_executable_with_function(root, 1821));
    let current = ProductKey::ExecutableEffects(fake_executable_with_function(root, 1822));
    let mut memo = ProductMemo::default();
    memo.unblock(ProductRequestId(NonZeroU64::MIN), &reader, prospective_dependency(&old));
    memo.unblock(
        ProductRequestId(NonZeroU64::MIN),
        &reader,
        prospective_dependency(&current),
    );
    assert_eq!(
        memo.pending_product_dependencies(&reader),
        Some(&prospective_dependency(&current))
    );
    assert!(!memo.product_readers.contains_key(&old));
}

#[test]
fn retained_validation_obeys_current_control_before_obsolete_children() {
    assert_current_control_ownership(false);
}

#[test]
fn retained_validation_refreshes_indirect_control_before_obsolete_children() {
    assert_current_control_ownership(true);
}

fn assert_current_control_ownership(indirect: bool) {
    for reverse_names in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(180);
        let key = |id| ProductKey::ExecutableEffects(fake_executable_with_function(root, id));
        let reader = key(1800);
        let selector = key(if reverse_names { 1801 } else { 1802 });
        let old_child = key(if reverse_names { 1802 } else { 1801 });
        let upstream = key(1803);
        let result =
            ProductValue::MaterializedExecutable(Rc::new(fake_effect_materialized(&fake_executable(root), &[], false)));
        let mut producers = OwnershipProducers {
            telemetry: &tel,
            types: fake_types(),
            calls: Vec::new(),
            formulas: HashMap::from([
                (
                    reader.clone(),
                    OwnershipFormula::Reader {
                        selector: selector.clone(),
                        child: old_child.clone(),
                        recursive: false,
                        value: result.clone(),
                    },
                ),
                (
                    selector.clone(),
                    if indirect {
                        OwnershipFormula::Copy(upstream.clone())
                    } else {
                        OwnershipFormula::Value(ownership_selected(true))
                    },
                ),
                (upstream.clone(), OwnershipFormula::Value(ownership_selected(true))),
                (old_child.clone(), OwnershipFormula::Value(ProductValue::Unit)),
            ]),
        };
        let mut driver = ProductDriver::new(&tel, root);
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &reader),
            PullOutcome::Produced(result.clone())
        );
        producers.calls.clear();
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &reader),
            PullOutcome::Produced(result.clone())
        );
        assert!(
            producers.calls.is_empty(),
            "same input must reuse without evaluating any formula"
        );
        let changed = if indirect { &upstream } else { &selector };
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [changed.clone()], &producers.types);
        let equal = ownership_pull(&mut driver, &mut producers, &reader);
        assert!(
            matches!(&equal, PullOutcome::Produced(ProductValue::MaterializedExecutable(value)) if matches!(&result, ProductValue::MaterializedExecutable(original) if Rc::ptr_eq(value, original)))
        );
        assert_eq!(driver.session().memo.generation(&reader), Some(1));
        assert!(
            !producers.calls.contains(&reader),
            "equal selector must not evaluate its reader"
        );
        producers.calls.clear();
        producers
            .formulas
            .insert(changed.clone(), OwnershipFormula::Value(ownership_selected(false)));
        producers
            .formulas
            .insert(old_child.clone(), OwnershipFormula::Unavailable);
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [changed.clone(), old_child.clone()], &producers.types);
        let outcome = ownership_pull(&mut driver, &mut producers, &reader);
        assert!(
            !producers.calls.contains(&old_child),
            "obsolete child was evaluated: indirect={indirect}, reverse_names={reverse_names}, calls={:?}",
            producers.calls
        );
        assert_eq!(outcome, PullOutcome::Produced(result));
        producers.calls.clear();
        producers
            .formulas
            .insert(changed.clone(), OwnershipFormula::Value(ownership_selected(true)));
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [changed.clone()], &producers.types);
        assert!(matches!(
            ownership_pull(&mut driver, &mut producers, &reader),
            PullOutcome::Failed(_)
        ));
        assert!(
            producers.calls.contains(&old_child),
            "a still-required unavailable child remains an error"
        );
    }
}

#[test]
fn retained_recursive_validation_preserves_each_members_control_ownership() {
    assert_recursive_control_ownership(false);
}

#[test]
fn retained_recursive_validation_refreshes_indirect_member_control() {
    assert_recursive_control_ownership(true);
}

fn assert_recursive_control_ownership(indirect: bool) {
    for reverse_names in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let root = RootId::for_test(181);
        let key = |id| ProductKey::ExecutableEffects(fake_executable_with_function(root, id));
        let first = key(if reverse_names { 1811 } else { 1812 });
        let second = key(if reverse_names { 1812 } else { 1811 });
        let selector = key(1814);
        let old_child = key(1813);
        let upstream = key(1815);
        let result =
            ProductValue::MaterializedExecutable(Rc::new(fake_effect_materialized(&fake_executable(root), &[], false)));
        let mut producers = OwnershipProducers {
            telemetry: &tel,
            types: fake_types(),
            calls: Vec::new(),
            formulas: HashMap::from([
                (
                    first.clone(),
                    OwnershipFormula::Reader {
                        selector: selector.clone(),
                        child: second.clone(),
                        recursive: true,
                        value: result.clone(),
                    },
                ),
                (
                    second.clone(),
                    OwnershipFormula::Recursive {
                        child: old_child.clone(),
                        peer: first.clone(),
                    },
                ),
                (
                    selector.clone(),
                    if indirect {
                        OwnershipFormula::Copy(upstream.clone())
                    } else {
                        OwnershipFormula::Value(ownership_selected(true))
                    },
                ),
                (upstream.clone(), OwnershipFormula::Value(ownership_selected(true))),
                (old_child.clone(), OwnershipFormula::Value(result.clone())),
            ]),
        };
        let mut driver = ProductDriver::new(&tel, root);
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &first),
            PullOutcome::Produced(result.clone())
        );
        assert!(
            driver.session().memo.get(&second).is_some(),
            "both recursive members settled"
        );
        producers.calls.clear();
        let changed = if indirect { &upstream } else { &selector };
        let changed_result =
            ProductValue::MaterializedExecutable(Rc::new(fake_effect_materialized(&fake_executable(root), &[], true)));
        producers
            .formulas
            .insert(old_child.clone(), OwnershipFormula::Value(changed_result.clone()));
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [old_child.clone()], &producers.types);
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &first),
            PullOutcome::Produced(changed_result.clone())
        );
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &second),
            PullOutcome::Produced(changed_result)
        );
        for member in [&first, &second] {
            assert_eq!(
                driver.session().memo.generation(member),
                Some(2),
                "still-recursive members must publish the changed fixed point together"
            );
        }
        producers.calls.clear();
        let _ = ownership_pull(&mut driver, &mut producers, &first);
        assert!(producers.calls.is_empty());
        producers
            .formulas
            .insert(old_child.clone(), OwnershipFormula::Value(result.clone()));
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [old_child.clone()], &producers.types);
        assert_eq!(
            ownership_pull(&mut driver, &mut producers, &first),
            PullOutcome::Produced(result.clone())
        );
        assert_eq!(
            driver.session().memo.generation(&first),
            Some(3),
            "effect narrowing must replace the recursive fixed point too"
        );
        producers.calls.clear();
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [changed.clone()], &producers.types);
        let equal = ownership_pull(&mut driver, &mut producers, &first);
        assert!(
            matches!(&equal, PullOutcome::Produced(ProductValue::MaterializedExecutable(value)) if matches!(&result, ProductValue::MaterializedExecutable(original) if Rc::ptr_eq(value, original)))
        );
        for member in [&first, &second] {
            assert_eq!(driver.session().memo.generation(member), Some(3));
            assert!(
                !producers.calls.contains(member),
                "equal selector must not evaluate recursive members"
            );
        }
        producers.calls.clear();
        producers
            .formulas
            .insert(changed.clone(), OwnershipFormula::Value(ownership_selected(false)));
        producers
            .formulas
            .insert(old_child.clone(), OwnershipFormula::Unavailable);
        driver
            .session_mut()
            .memo
            .invalidate_products(&tel, [changed.clone(), old_child.clone()], &producers.types);
        let outcome = ownership_pull(&mut driver, &mut producers, &first);
        assert!(
            !producers.calls.contains(&old_child),
            "another member's obsolete child was evaluated: reverse_names={reverse_names}, calls={:?}",
            producers.calls
        );
        assert_eq!(outcome, PullOutcome::Produced(result));
        assert!(
            !producers.calls.contains(&second),
            "removed recursive member must not evaluate"
        );
    }
}
