use super::*;
use crate::any_value::ClosureDenotationId;
use crate::process::Node;

fn named(name: &str) -> Arc<FunctionDenotation> {
    Arc::new(FunctionDenotation {
        origin: FunctionOrigin::Named {
            module: None,
            name: name.into(),
        },
        arity: 0,
    })
}

#[test]
fn binary_table_roundtrip_preserves_typed_origins_and_ids() {
    let owner = Arc::new(FunctionDenotation::named(
        Some(ModuleName::from_segments(vec!["Outer".into(), "Inner".into()])),
        "make".into(),
        2,
    ));
    let generated = Arc::new(FunctionDenotation {
        arity: 1,
        origin: FunctionOrigin::Generated {
            owner: Arc::clone(&owner),
            occurrence: LambdaOccurrence::from_u32(7),
        },
    });
    let nested = Arc::new(FunctionDenotation {
        arity: 3,
        origin: FunctionOrigin::Generated {
            owner: generated,
            occurrence: LambdaOccurrence::from_u32(4),
        },
    });
    let table = vec![
        (ClosureDenotationId::user(8), nested),
        (ClosureDenotationId::user(2), owner),
        (ClosureDenotationId::user(9), named("root")),
    ];
    let bytes = encode_closure_denotations(&table).unwrap();
    assert_eq!(decode_closure_denotations(&bytes).unwrap(), table);
    assert_eq!(
        decode_closure_denotations(&encode_closure_denotations(&[]).unwrap()).unwrap(),
        vec![]
    );
    for cut in 0..bytes.len() {
        assert!(
            decode_closure_denotations(&bytes[..cut]).is_err(),
            "truncated prefix {cut} must fail"
        );
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(
        decode_closure_denotations(&trailing).is_err(),
        "trailing bytes cannot be silently discarded"
    );
}

#[test]
fn binary_table_rejects_invalid_tags_identity_and_text() {
    let table = vec![(ClosureDenotationId::user(0), named("f"))];
    let bytes = encode_closure_denotations(&table).unwrap();
    for (offset, value) in [(12, 2), (13, 3), (18, 255)] {
        let mut corrupt = bytes.clone();
        corrupt[offset] = value;
        assert!(decode_closure_denotations(&corrupt).is_err());
    }
    let mut internal = bytes;
    internal[4..8].copy_from_slice(&u32::MAX.to_ne_bytes());
    assert!(decode_closure_denotations(&internal).is_err());
    assert!(encode_closure_denotations(&[(ClosureDenotationId::INTERNAL, named("f"))]).is_err());
    let qualified = vec![(
        ClosureDenotationId::user(0),
        Arc::new(FunctionDenotation::named(
            Some(ModuleName::from_segments(vec!["M".into()])),
            "f".into(),
            0,
        )),
    )];
    let mut empty_module = encode_closure_denotations(&qualified).unwrap();
    empty_module[14..18].copy_from_slice(&0u32.to_ne_bytes());
    assert!(decode_closure_denotations(&empty_module).is_err());
    let mut empty_segment = encode_closure_denotations(&qualified).unwrap();
    empty_segment[18..22].copy_from_slice(&0u32.to_ne_bytes());
    assert!(decode_closure_denotations(&empty_segment).is_err());
}

#[test]
fn closure_order_ignores_mint_order_and_retains_existing_origins() {
    let first = Node::empty();
    let second = Node::empty();
    let zero = ClosureDenotationId::user(0);
    let one = ClosureDenotationId::user(1);
    let alpha = named("alpha");
    let zulu = named("zulu");
    first.register_closure_denotation(zero, Arc::clone(&zulu));
    first.register_closure_denotation(one, Arc::clone(&alpha));
    second.register_closure_denotation(zero, Arc::clone(&alpha));
    second.register_closure_denotation(one, Arc::clone(&zulu));
    assert_eq!(first.compare_closure_denotations(one, zero), Ordering::Less);
    assert_eq!(second.compare_closure_denotations(zero, one), Ordering::Less);
    first.register_closure_denotation(ClosureDenotationId::user(9), named("middle"));
    first.register_closure_denotation(one, Arc::clone(&alpha));
    assert_eq!(first.compare_closure_denotations(one, zero), Ordering::Less);
    assert!(Arc::ptr_eq(&alpha, &first.closure_denotation(one)));
}

#[test]
#[should_panic(expected = "internal continuation")]
fn internal_continuations_have_no_user_order() {
    Node::empty().compare_closure_denotations(ClosureDenotationId::INTERNAL, ClosureDenotationId::INTERNAL);
}

#[test]
fn generated_order_uses_owner_then_occurrence_then_arity() {
    let lambda = |owner, occurrence, arity| FunctionDenotation {
        origin: FunctionOrigin::Generated {
            owner,
            occurrence: LambdaOccurrence::from_u32(occurrence),
        },
        arity,
    };
    let early_owner = named("alpha");
    let late_owner = named("zulu");
    let later_in_early_owner = lambda(Arc::clone(&early_owner), 9, 2);
    let first_in_late_owner = lambda(late_owner, 0, 0);
    assert_eq!(later_in_early_owner.semantic_cmp(&first_in_late_owner), Ordering::Less);
    assert_eq!(
        lambda(Arc::clone(&early_owner), 0, 9).semantic_cmp(&later_in_early_owner),
        Ordering::Less
    );
    assert_eq!(
        lambda(early_owner, 9, 1).semantic_cmp(&later_in_early_owner),
        Ordering::Less
    );
}

#[test]
fn module_segment_boundaries_are_part_of_source_identity() {
    let one_segment = FunctionDenotation::named(Some(ModuleName::from_segments(vec!["A.B".into()])), "f".into(), 0);
    let two_segments = FunctionDenotation::named(
        Some(ModuleName::from_segments(vec!["A".into(), "B".into()])),
        "f".into(),
        0,
    );
    assert_eq!(
        one_segment.label(),
        two_segments.label(),
        "display spelling deliberately loses the boundary"
    );
    assert_ne!(
        one_segment.semantic_cmp(&two_segments),
        Ordering::Equal,
        "source module segments retain the boundary"
    );
}
