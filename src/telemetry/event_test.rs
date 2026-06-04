use super::*;
use crate::telemetry::value::opaque;

#[test]
fn measurements_macro_empty() {
    let m: Measurements<'_> = measurements! {};
    assert_eq!(m.len(), 0);
    assert_eq!(m.len(), 0);
}

#[test]
fn measurements_macro_single() {
    let m = measurements! { count: 3i64 };
    assert_eq!(m.len(), 1);
    assert!(matches!(m.get("count"), Some(Value::I64(3))));
}

#[test]
fn measurements_macro_multi_with_trailing_comma() {
    let m = measurements! { count: 3i64, ns: 1421u64, };
    assert_eq!(m.len(), 2);
    assert!(matches!(m.get("count"), Some(Value::I64(3))));
    assert!(matches!(m.get("ns"), Some(Value::U64(1421))));
}

#[test]
fn metadata_macro_handles_strings_and_bools() {
    let m = metadata! { name: "lex", enabled: true };
    assert_eq!(m.len(), 2);
    assert!(matches!(m.get("name"), Some(Value::Str(_))));
    assert!(matches!(m.get("enabled"), Some(Value::Bool(true))));
}

#[test]
fn metadata_macro_owned_string_expression() {
    let n: String = format!("fn_{}", 42);
    let m = metadata! { fn_name: n };
    assert!(matches!(m.get("fn_name"), Some(Value::Str(_))));
}

#[test]
fn from_pairs_preserves_order() {
    let m = Measurements::from_pairs([("a", Value::I64(1)), ("b", Value::I64(2)), ("c", Value::I64(3))]);
    let keys: Vec<_> = m.iter().map(|(k, _)| *k).collect();
    assert_eq!(keys, vec!["a", "b", "c"]);
}

#[test]
fn get_returns_none_for_missing_key() {
    let m = measurements! { count: 1i64 };
    assert!(m.get("absent").is_none());
}

#[test]
fn over_four_entries_overflows_inline_storage() {
    // SmallVec inline capacity is 4 — make sure overflow still works.
    let m = measurements! { a: 1i64, b: 2i64, c: 3i64, d: 4i64, e: 5i64 };
    assert_eq!(m.len(), 5);
    assert!(matches!(m.get("e"), Some(Value::I64(5))));
}

#[test]
fn durable_owned_skips_opaque_values() {
    let module_like = 7usize;
    let md = metadata! { name: "lowered", module: opaque(&module_like) };
    let owned = md.durable_owned();
    assert!(matches!(owned.get("name"), Some(Value::Str(_))));
    assert!(owned.get("module").is_none());
}
