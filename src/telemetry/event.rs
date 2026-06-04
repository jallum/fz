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
#[path = "event_test.rs"]
mod event_test;
