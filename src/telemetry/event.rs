//! Event payload containers and the construction macros.
//!
//! `Measurements` and `Metadata` are the same shape — a small inline-allocated
//! vector of `(static-key, Value)` pairs — but stay as distinct types so emit
//! sites and handlers can tell numeric measurements apart from contextual
//! metadata without convention or comment.
//!
//! The `measurements!` and `metadata!` macros wrap construction so callers
//! write `measurements!{count: 3, ns: 1421}` instead of building the vector
//! by hand.

use smallvec::SmallVec;

use super::value::Value;

pub type KvVec<'a> = SmallVec<[(&'static str, Value<'a>); 4]>;

macro_rules! kv_newtype {
    ($name:ident) => {
        #[derive(Debug, Clone, Default)]
        pub struct $name<'a>(pub KvVec<'a>);

        impl<'a> $name<'a> {
            pub fn new() -> Self {
                Self(SmallVec::new())
            }

            pub fn from_pairs(pairs: impl IntoIterator<Item = (&'static str, Value<'a>)>) -> Self {
                Self(pairs.into_iter().collect())
            }

            pub fn iter(&self) -> std::slice::Iter<'_, (&'static str, Value<'a>)> {
                self.0.iter()
            }

            pub fn get(&self, key: &str) -> Option<&Value<'a>> {
                self.0.iter().find_map(|(k, v)| (*k == key).then_some(v))
            }

            #[cfg(test)]
            pub fn durable_owned(&self) -> $name<'static> {
                $name(
                    self.0
                        .iter()
                        .filter_map(|(k, v)| v.to_owned_durable().map(|v| (*k, v)))
                        .collect(),
                )
            }

            #[cfg(test)]
            pub fn len(&self) -> usize {
                self.0.len()
            }
        }
    };
}

kv_newtype!(Measurements);
kv_newtype!(Metadata);

/// Build a `Measurements` value from a key/value list.
///
/// ```ignore
/// measurements!{count: 3, elapsed_ns: 1421u64}
/// ```
///
/// Each key is an identifier (stringified via `stringify!`); each value
/// is anything implementing `Into<Value>`. Empty `measurements!{}` is valid.
#[macro_export]
macro_rules! measurements {
    () => { $crate::telemetry::Measurements::new() };
    ($($k:ident: $v:expr),+ $(,)?) => {
        $crate::telemetry::Measurements::from_pairs([
            $((stringify!($k), $crate::telemetry::Value::from($v))),+
        ])
    };
}

/// Build a `Metadata` value from a key/value list. Same shape as
/// `measurements!`; kept separate so the two channels stay typed-apart.
#[macro_export]
macro_rules! metadata {
    () => { $crate::telemetry::Metadata::new() };
    ($($k:ident: $v:expr),+ $(,)?) => {
        $crate::telemetry::Metadata::from_pairs([
            $((stringify!($k), $crate::telemetry::Value::from($v))),+
        ])
    };
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let m = Measurements::from_pairs([
            ("a", Value::I64(1)),
            ("b", Value::I64(2)),
            ("c", Value::I64(3)),
        ]);
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
        let md =
            metadata! { name: "lowered", module: crate::telemetry::value::opaque(&module_like) };
        let owned = md.durable_owned();
        assert!(matches!(owned.get("name"), Some(Value::Str(_))));
        assert!(owned.get("module").is_none());
    }
}
