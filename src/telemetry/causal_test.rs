use super::*;

#[test]
fn dependency_identity_preserves_the_complete_nested_product_key() {
    let raw = serde_json::json!({
        "kind": "Product", "root_id": 7, "use": "settled", "revision": 3,
        "product": {"kind": "test_product", "revision": 2, "nested": {"changed": true}}
    });
    assert_eq!(
        RawIdentity::new(&raw).0,
        serde_json::json!({
            "kind": "Product", "root_id": 7,
            "product": {"kind": "test_product", "revision": 2, "nested": {"changed": true}}
        })
    );
}

#[test]
fn construction_target_surfaces_use_the_trace_type_dictionary() {
    let canon = CanonTables {
        types: HashMap::from([(7, "int".to_string()), (8, "atom".to_string())]),
        functions: HashMap::new(),
    };
    let raw = serde_json::json!({
        "kind": "DeriveCallableConstructionTarget",
        "surface": [7, 8],
    });

    assert_eq!(
        serde_json::from_str::<Json>(&RawIdentity::new(&raw).canonical(&canon)).unwrap(),
        serde_json::json!({
            "kind": "DeriveCallableConstructionTarget",
            "surface": ["int", "atom"],
        })
    );
    let mut references = References::default();
    references.walk(&raw);
    assert_eq!(references.types, vec![7, 8]);
}

#[test]
fn raw_product_identity_removes_only_its_renderer_annotation() {
    let raw = serde_json::json!({
        "opaque_type": "fz::compiler2::pull::ProductKey",
        "kind": "runtime_demand",
        "use": "settled",
        "revision": 3,
        "old_revision": 2,
        "new_revision": 3,
        "settled": true,
        "changed": false,
        "waits": [{"use": "current", "revision": 7}],
        "nested": {"opaque_type": "semantic nested field", "changed": true},
    });
    let normalized = RawProductKey::new(&raw);
    assert_eq!(
        normalized.raw,
        serde_json::json!({
            "kind": "runtime_demand",
            "use": "settled",
            "revision": 3,
            "old_revision": 2,
            "new_revision": 3,
            "settled": true,
            "changed": false,
            "waits": [{"use": "current", "revision": 7}],
            "nested": {"opaque_type": "semantic nested field", "changed": true},
        })
    );

    let mut other_renderer = raw.clone();
    other_renderer["opaque_type"] = Json::String("another renderer type".to_string());
    assert_eq!(normalized, RawProductKey::new(&other_renderer));
    for field in [
        "use",
        "revision",
        "old_revision",
        "new_revision",
        "settled",
        "changed",
        "waits",
        "nested",
    ] {
        let mut changed = raw.clone();
        changed[field] = Json::Null;
        assert_ne!(normalized, RawProductKey::new(&changed), "{field} remains semantic");
    }
}

#[test]
fn canonical_product_identity_substitutes_ids_without_filtering_fields() {
    let canon = CanonTables {
        types: HashMap::from([(7, "int".to_string())]),
        functions: HashMap::from([(11, "module.function".to_string())]),
    };
    let raw = serde_json::json!({
        "opaque_type": "renderer annotation",
        "kind": "runtime_demand",
        "arrow": 7,
        "function_id": 11,
        "input": [7],
        "use": "settled",
        "revision": 3,
        "settled": true,
        "changed": false,
        "nested": {
            "opaque_type": "semantic nested field",
            "changed": true,
            "items": [{"use": "current", "revision": 9}],
        },
    });
    let product = RawProductKey::new(&raw);
    let canonical = product.canonical_identity(&canon);
    assert_eq!(
        serde_json::from_str::<Json>(&canonical).unwrap(),
        serde_json::json!({
            "kind": "runtime_demand",
            "arrow": "int",
            "function_id": "module.function",
            "input": ["int"],
            "use": "settled",
            "revision": 3,
            "settled": true,
            "changed": false,
            "nested": {
                "opaque_type": "semantic nested field",
                "changed": true,
                "items": [{"use": "current", "revision": 9}],
            },
        })
    );

    let mut renderer_variant = raw.clone();
    renderer_variant["opaque_type"] = Json::String("other renderer".to_string());
    assert_eq!(
        canonical,
        RawProductKey::new(&renderer_variant).canonical_identity(&canon)
    );
    for field in ["use", "revision", "settled", "changed", "nested"] {
        let mut variant = raw.clone();
        variant[field] = Json::Null;
        assert_ne!(
            canonical,
            RawProductKey::new(&variant).canonical_identity(&canon),
            "canonical reporting must preserve {field}"
        );
    }

    let mut nested_opaque_variant = raw.clone();
    nested_opaque_variant["nested"]["opaque_type"] = Json::String("other semantic nested field".to_string());
    assert_ne!(
        canonical,
        RawProductKey::new(&nested_opaque_variant).canonical_identity(&canon)
    );
    let mut nested_array_variant = raw.clone();
    nested_array_variant["nested"]["items"][0]["changed"] = Json::Bool(true);
    assert_ne!(
        canonical,
        RawProductKey::new(&nested_array_variant).canonical_identity(&canon)
    );

    let mut report = CausalReport {
        canon,
        ..CausalReport::default()
    };
    report.products.insert(
        product,
        ProductWork {
            requests: 1,
            ..ProductWork::default()
        },
    );
    for variant in [
        {
            let mut variant = raw;
            variant["use"] = Json::String("current".to_string());
            variant
        },
        nested_opaque_variant,
        nested_array_variant,
    ] {
        report.products.insert(
            RawProductKey::new(&variant),
            ProductWork {
                requests: 1,
                ..ProductWork::default()
            },
        );
    }
    let requests = report
        .canonical_multiset()
        .into_iter()
        .filter(|(key, _)| key.starts_with("product\u{1}") && key.ends_with("\u{1}requests"))
        .collect::<Vec<_>>();
    assert_eq!(
        requests.len(),
        4,
        "canonical multiset must retain top-level, nested-object, and nested-array product state"
    );
    assert!(requests.iter().all(|(_, count)| *count == 1));
}
