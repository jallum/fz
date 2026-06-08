use super::*;
#[test]
fn from_impls_cover_primitives() {
    assert!(matches!(Value::from(3i64), Value::I64(3)));
    assert!(matches!(Value::from(3i32), Value::I64(3)));
    assert!(matches!(Value::from(3u64), Value::U64(3)));
    assert!(matches!(Value::from(3u32), Value::U64(3)));
    assert!(matches!(Value::from(3usize), Value::U64(3)));
    assert!(matches!(Value::from(2.5f64), Value::F64(_)));
    assert!(matches!(Value::from(true), Value::Bool(true)));
}

#[test]
fn str_from_static_is_borrowed() {
    match Value::from("hello") {
        Value::Str(Cow::Borrowed("hello")) => {}
        v => panic!("expected borrowed str, got {:?}", v),
    }
}

#[test]
fn str_from_string_is_owned() {
    let s = String::from("dynamic");
    match Value::from(s) {
        Value::Str(Cow::Owned(s)) => assert_eq!(s, "dynamic"),
        v => panic!("expected owned str, got {:?}", v),
    }
}

#[test]
fn bytes_round_trip() {
    let v: Value = vec![1u8, 2, 3].into();
    match v {
        Value::Bytes(b) => assert_eq!(&*b, &[1, 2, 3]),
        other => panic!("expected bytes, got {:?}", other),
    }
}

#[test]
fn is_numeric_classifies_correctly() {
    assert!(Value::I64(1).is_numeric());
    assert!(Value::U64(1).is_numeric());
    assert!(Value::F64(1.0).is_numeric());
    assert!(!Value::Bool(true).is_numeric());
    assert!(!Value::from("x").is_numeric());
}

#[test]
fn tag_is_stable_lower_snake() {
    assert_eq!(Value::I64(0).tag(), "i64");
    assert_eq!(Value::U64(0).tag(), "u64");
    assert_eq!(Value::F64(0.0).tag(), "f64");
    assert_eq!(Value::Bool(false).tag(), "bool");
    assert_eq!(Value::from("s").tag(), "str");
    assert_eq!(Value::from(vec!["a".to_string()]).tag(), "str_seq");
    assert_eq!(Value::Bytes(Arc::from(vec![])).tag(), "bytes");
}

#[test]
fn string_sequence_from_vec_round_trips() {
    match Value::from(vec!["a".to_string(), "b".to_string()]) {
        Value::StrSeq(values) => assert_eq!(&*values, &["a".to_string(), "b".to_string()]),
        other => panic!("expected string sequence, got {:?}", other),
    }
}

#[test]
fn opaque_round_trip_downcasts_during_event_lifetime() {
    let n = 42usize;
    let v = Value::opaque(&n);
    assert_eq!(v.tag(), "opaque");
    assert_eq!(v.downcast_ref::<usize>(), Some(&42usize));
    assert!(v.downcast_ref::<String>().is_none());
    let opaque = match v {
        Value::Opaque(opaque) => opaque,
        other => panic!("expected opaque value, got {other:?}"),
    };
    assert_eq!(opaque.type_name(), std::any::type_name::<usize>());
    assert!(
        opaque.debug_value().is_none(),
        "plain opaque values should stay debug-free"
    );
}

#[test]
fn opaque_debug_retains_borrowed_debug_rendering() {
    let n = 42usize;
    let v = Value::opaque_debug(&n);
    let opaque = match v {
        Value::Opaque(opaque) => opaque,
        other => panic!("expected opaque value, got {other:?}"),
    };
    assert_eq!(
        format!(
            "{:?}",
            opaque
                .debug_value()
                .expect("opaque_debug should preserve a borrowed debug formatter")
        ),
        "42"
    );
}

#[test]
fn opaque_is_not_durable() {
    let n = 42usize;
    let v = Value::opaque(&n);
    assert!(v.to_owned_durable().is_none());
}
