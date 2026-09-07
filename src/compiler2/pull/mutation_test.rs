fn mutation_key(id: u32) -> ProductKey {
    ProductKey::RootBackendProduct(RootId::for_test(id))
}

fn capture_mutation_work(tel: &ConfiguredTelemetry) -> Rc<Cell<ProductValidation>> {
    let captured = Rc::new(Cell::new(ProductValidation::default()));
    let observed = Rc::clone(&captured);
    tel.attach_raw_event2::<ProductKey, ProductValidation, _>(
        &["fz", "compiler2", "pull", "product", "validation"],
        move |_, _, _, _, work| {
            let mut total = observed.get();
            total.include(*work);
            observed.set(total);
        },
    );
    captured
}

#[test]
fn mutation_admission_keeps_single_products_inline_and_never_clones_rejected_keys() {
    struct Key {
        id: u32,
        input: Box<[u8]>,
        clones: Rc<Cell<u64>>,
        hashes: Rc<Cell<u64>>,
    }
    impl Clone for Key {
        fn clone(&self) -> Self {
            self.clones.set(self.clones.get() + 1);
            Self {
                id: self.id,
                input: self.input.clone(),
                clones: Rc::clone(&self.clones),
                hashes: Rc::clone(&self.hashes),
            }
        }
    }
    impl PartialEq for Key {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }
    impl Eq for Key {}
    impl std::hash::Hash for Key {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.hashes.set(self.hashes.get() + 1);
            self.id.hash(state);
        }
    }
    let clones = Rc::new(Cell::new(0));
    let hashes = Rc::new(Cell::new(0));
    let key = |id| Key {
        id,
        input: vec![0; 32].into_boxed_slice(),
        clones: Rc::clone(&clones),
        hashes: Rc::clone(&hashes),
    };
    let first = key(0);
    let mut admissions = MutationAdmissions::Empty;
    let strengths = [
        ReaderMutation::Invalidate,
        ReaderMutation::Dirty,
        ReaderMutation::Refresh,
    ];
    for mutation in strengths {
        assert!(admissions.admit(mutation, &first));
    }
    for mutation in strengths {
        assert!(!admissions.admit(mutation, &first));
    }
    assert_eq!(clones.get(), 1, "all strengths share one owned key");
    assert_eq!(hashes.get(), 0, "a single-product wave never enters a hash table");
    let MutationAdmissions::One(stored, mask) = &admissions else {
        panic!("one key stays inline")
    };
    assert_eq!(*mask, 7);
    let first_storage = stored.input.as_ptr();
    let size = 512;
    for id in 1..size {
        let next = key(id);
        for mutation in strengths {
            assert!(admissions.admit(mutation, &next));
        }
        for mutation in strengths {
            assert!(!admissions.admit(mutation, &next));
        }
    }
    assert_eq!(
        clones.get(),
        u64::from(size),
        "promotion and rejected strengths never clone an owned key"
    );
    assert!(
        hashes.get() <= u64::from(size) * 12,
        "all actual key hashes, including promotion and growth rehashing, remain linear: {}",
        hashes.get()
    );
    let MutationAdmissions::Many(stored) = &admissions else {
        panic!("multiple keys share one map")
    };
    assert_eq!(stored.len(), size as usize);
    assert_eq!(
        stored.keys().find(|key| key.id == 0).unwrap().input.as_ptr(),
        first_storage,
        "promotion moves the inline key"
    );
    let before = clones.get();
    for mutation in strengths {
        assert!(!admissions.admit(mutation, &first));
    }
    assert_eq!(
        clones.get(),
        before,
        "borrowed duplicate lookup performs zero key copies"
    );
}

fn mutation_positioned_key(types: &mut super::super::Types, id: u32) -> ProductKey {
    let executable = fake_executable_with_function(RootId::for_test(100), id);
    let mut symbol = executable_symbol_for_test(&executable);
    symbol.activation.input = vec![types.any(); 32].into_boxed_slice();
    ProductKey::TransportShape(TransportPosition::ExecutableReturn { executable: symbol })
}

fn mutation_input(key: &ProductKey) -> *const super::super::Ty {
    let ProductKey::TransportShape(position) = key else {
        panic!("positioned key")
    };
    position.executable().activation.input.as_ptr()
}

#[test]
fn mutation_heap_reuses_owned_positioned_keys_and_returns_rejected_escalations() {
    let mut types = fake_types();
    let mut seeds = Vec::with_capacity(8);
    let mut originals = Vec::new();
    for id in [3, 1, 2] {
        let key = mutation_positioned_key(&mut types, id);
        originals.push((key.clone(), mutation_input(&key)));
        seeds.push((ReaderMutation::Dirty, key));
    }
    let buffer = seeds.as_ptr();
    let mut wave = ProductMutationWave::new(seeds, &types);
    let values = std::mem::replace(&mut wave.pending, OrderedWorklist::from_sorted(Vec::new())).into_values();
    assert_eq!(
        values.as_ptr(),
        buffer,
        "initial admission and ordering retain the seed allocation"
    );
    assert_eq!(values.capacity(), 8);
    wave.pending = OrderedWorklist::from_sorted(values);
    let (mutation, selected) = wave.pop(&types).unwrap();
    assert_eq!(mutation, ReaderMutation::Dirty);
    assert_eq!(
        selected, originals[1].0,
        "typed product ordering selects the smallest key"
    );
    let input = mutation_input(&selected);
    assert_eq!(input, originals[1].1);
    assert!(wave.push(ReaderMutation::Invalidate, selected, &types).is_none());
    let (mutation, selected) = wave.pop(&types).unwrap();
    assert_eq!(
        mutation,
        ReaderMutation::Invalidate,
        "a newly stronger same-key mutation competes immediately"
    );
    assert_eq!(
        mutation_input(&selected),
        input,
        "pending escalation moves its original positioned input"
    );
    let rejected = wave.push(ReaderMutation::Invalidate, selected, &types).unwrap();
    assert_eq!(
        mutation_input(&rejected),
        input,
        "rejected owned escalation returns its original key for attribution"
    );
    let MutationAdmissions::Many(admissions) = &wave.admissions else {
        unreachable!()
    };
    let map_input = mutation_input(admissions.get_key_value(&rejected).unwrap().0);
    wave.push_borrowed(ReaderMutation::Refresh, &rejected, &types);
    wave.push_borrowed(ReaderMutation::Refresh, &rejected, &types);
    let (mutation, selected) = wave.pop(&types).unwrap();
    assert_eq!(mutation, ReaderMutation::Refresh);
    assert_eq!(selected, rejected);
    let MutationAdmissions::Many(admissions) = &wave.admissions else {
        unreachable!()
    };
    assert_eq!(
        mutation_input(admissions.get_key_value(&selected).unwrap().0),
        map_input,
        "all three strengths share the same map-owned input"
    );
    while let Some((_, key)) = wave.pop(&types) {
        let (_, input) = originals.iter().find(|(expected, _)| *expected == key).unwrap();
        assert_eq!(
            mutation_input(&key),
            *input,
            "heap selection moves each original key without cloning it"
        );
    }
    assert_eq!(wave.work.mutation_pops, 5);
    assert_eq!(wave.work.mutation_admissions, 7);
}

#[test]
fn mutation_wave_selection_is_subquadratic_in_independent_and_repeated_seeds() {
    let mut regressions = Vec::new();
    for size in [32_u32, 128, 512] {
        for repetitions in [1, 4] {
            let tel = ConfiguredTelemetry::new();
            let captured = capture_mutation_work(&tel);
            let types = fake_types();
            let mut memo = ProductMemo::default();
            let keys = (0..size).map(mutation_key).collect::<Vec<_>>();
            for key in &keys {
                finish_test_product(&mut memo, key, ProductValue::Unit, []);
                memo.observed_products.insert(key.clone());
            }
            let seeds = (0..repetitions)
                .flat_map(|_| keys.iter().rev().cloned())
                .map(|key| (ReaderMutation::Invalidate, key))
                .collect();
            memo.mutate_product_wave(&tel, seeds, &types);
            let work = captured.get();
            let comparisons = work.ordering_comparisons;
            assert_eq!(work.mutation_admissions, u64::from(size * repetitions));
            assert_eq!(
                work.mutation_pops,
                u64::from(size),
                "duplicate seeds never repeat selection"
            );
            assert_eq!(work.mutation_edges, 0);
            assert_eq!(
                memo.external_changes
                    .iter()
                    .map(|change| &change.key)
                    .collect::<Vec<_>>(),
                keys.iter().collect::<Vec<_>>()
            );
            assert!(memo.produced.is_empty());
            let bound = u64::from(size) * u64::from(size.ilog2() + 1) * 4 + u64::from(size * repetitions);
            if comparisons > bound {
                regressions.push(format!(
                    "size={size}, repetitions={repetitions}, work={work:?}, comparison_bound={bound}"
                ));
            }
        }
    }
    assert!(
        regressions.is_empty(),
        "selection is bounded and duplicates never enter the heap:\n{}",
        regressions.join("\n")
    );
}

#[test]
fn mutation_wave_diamonds_reject_shared_readers_before_selection() {
    let mut regressions = Vec::new();
    for size in [32_u32, 128, 512] {
        let tel = ConfiguredTelemetry::new();
        let captured = capture_mutation_work(&tel);
        let types = fake_types();
        let mut memo = ProductMemo::default();
        let source = mutation_key(0);
        let leaves = (1..=size).map(mutation_key).collect::<Vec<_>>();
        let sink = mutation_key(size + 1);
        finish_test_product(&mut memo, &source, ProductValue::Unit, []);
        for leaf in &leaves {
            finish_test_product(&mut memo, leaf, ProductValue::Unit, [source.clone()]);
        }
        finish_test_product(&mut memo, &sink, ProductValue::Unit, leaves.iter().cloned());
        memo.mutate_product_wave(&tel, vec![(ReaderMutation::Invalidate, source)], &types);
        let work = captured.get();
        assert_eq!(work.mutation_admissions, u64::from(size * 2 + 1));
        assert_eq!(work.mutation_pops, u64::from(size + 2));
        assert_eq!(work.mutation_edges, u64::from(size * 2));
        assert_eq!(memo.generation(&sink), Some(1));
        assert!(memo.dirty_descendants.contains(&sink));
        let bound = u64::from(size + 2) * u64::from(size.ilog2() + 2) * 4;
        if work.ordering_comparisons > bound {
            regressions.push(format!("size={size}, work={work:?}, comparison_bound={bound}"));
        }
    }
    assert!(
        regressions.is_empty(),
        "shared edges may attempt admission repeatedly, but never repeat selection:\n{}",
        regressions.join("\n")
    );
}

#[test]
fn mutation_wave_preserves_every_strength_and_pending_cycle_escalation() {
    for reverse in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let captured = capture_mutation_work(&tel);
        let types = fake_types();
        let mut memo = ProductMemo::default();
        let key = mutation_key(10);
        finish_test_product(&mut memo, &key, ProductValue::Unit, []);
        memo.observed_products.insert(key.clone());
        let mut seeds = [
            ReaderMutation::Refresh,
            ReaderMutation::Dirty,
            ReaderMutation::Invalidate,
        ]
        .into_iter()
        .map(|mutation| (mutation, key.clone()))
        .collect::<Vec<_>>();
        if reverse {
            seeds.reverse();
        }
        memo.mutate_product_wave(&tel, seeds, &types);
        assert_eq!(captured.get().mutation_pops, 3, "one product is not one mutation");
        assert_eq!(memo.external_changes.len(), 1);
        assert!(memo.get(&key).is_none(), "Invalidate wins over both Dirty and Refresh");
        assert_eq!(
            memo.external_changes[0].new_revision,
            Some(1),
            "the displaced answer retains its external generation"
        );
        assert!(!memo.external_changes[0].new_settled);
        assert!(
            !memo.dirty_descendants.contains(&key),
            "Refresh runs after Dirty at equal typed key"
        );

        let [first, second] = [1, 2].map(mutation_key);
        for (owner, dependency) in [(&first, &second), (&second, &first)] {
            memo.unblock(
                ProductRequestId(NonZeroU64::MIN),
                owner,
                prospective_dependency(dependency),
            );
        }
        captured.set(ProductValidation::default());
        let mut seeds = vec![(ReaderMutation::Dirty, first), (ReaderMutation::Dirty, second)];
        if reverse {
            seeds.reverse();
        }
        memo.mutate_product_wave(&tel, seeds, &types);
        assert_eq!(
            captured.get().mutation_pops,
            4,
            "each pending Dirty escalates to its distinct Invalidate"
        );
        assert!(memo.pending_dependencies.is_empty());
        assert!(
            memo.product_readers.is_empty(),
            "the cycle's obsolete subscriptions are withdrawn"
        );
    }
}

#[test]
fn mutation_wave_cannot_refresh_a_reader_invalidated_by_the_same_group() {
    for reverse in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let captured = capture_mutation_work(&tel);
        let types = fake_types();
        let mut memo = ProductMemo::default();
        let [equal, changed, reader] = [10, 20, 30].map(mutation_key);
        for key in [&equal, &changed] {
            finish_test_product(&mut memo, key, ProductValue::Unit, []);
        }
        finish_test_product(&mut memo, &reader, ProductValue::Unit, [equal.clone(), changed.clone()]);
        memo.observed_products.insert(reader.clone());
        for key in [&equal, &changed] {
            assert!(memo.begin(key.clone()));
        }
        let mut members = vec![
            (equal.clone(), ProductValue::Unit, ProductDependencies::default()),
            (
                changed.clone(),
                ProductValue::ExecutableEffects(EffectSummary::default()),
                ProductDependencies::default(),
            ),
        ];
        if reverse {
            members.reverse();
        }
        assert!(finish_test_group(&mut memo, &tel, &equal, members, &types));
        assert_eq!(memo.generation(&equal), Some(1));
        assert_eq!(memo.generation(&changed), Some(2));
        assert_eq!(captured.get().mutation_admissions, 2);
        assert_eq!(
            captured.get().mutation_pops,
            2,
            "equal and changed inputs retain distinct reader mutations"
        );
        assert!(
            memo.get(&reader).is_none(),
            "Refresh cannot resurrect the invalidated answer"
        );
        assert!(
            memo.product_readers.is_empty(),
            "the obsolete reader subscriptions are withdrawn"
        );
        assert_eq!(memo.external_changes.len(), 1);
        assert_eq!(memo.external_changes[0].key, reader);
        assert_eq!(memo.external_changes[0].new_revision, Some(1));
        assert!(!memo.external_changes[0].new_settled);
    }
}

#[test]
fn a_newly_discovered_smaller_reader_precedes_the_remaining_seed() {
    for reverse in [false, true] {
        let tel = ConfiguredTelemetry::new();
        let types = fake_types();
        let mut memo = ProductMemo::default();
        let [reader, first, second] = [1, 10, 20].map(mutation_key);
        finish_test_product(&mut memo, &first, ProductValue::Unit, []);
        finish_test_product(&mut memo, &second, ProductValue::Unit, []);
        finish_test_product(&mut memo, &reader, ProductValue::Unit, [first.clone()]);
        memo.observed_products
            .extend([reader.clone(), first.clone(), second.clone()]);
        let mut seeds = vec![
            (ReaderMutation::Invalidate, first.clone()),
            (ReaderMutation::Invalidate, second.clone()),
        ];
        if reverse {
            seeds.reverse();
        }
        memo.mutate_product_wave(&tel, seeds, &types);
        assert_eq!(
            memo.external_changes
                .iter()
                .map(|change| &change.key)
                .collect::<Vec<_>>(),
            vec![&first, &reader, &second],
            "newly exposed readers compete immediately; sorting only the seed batch is insufficient"
        );
        assert_eq!(
            memo.generation(&reader),
            Some(1),
            "dirtiness retains the reader's value"
        );
        assert!(!memo.external_state(&reader).settled);
    }
}
