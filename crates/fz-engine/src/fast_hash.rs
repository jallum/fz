//! The engine's hash tables: foldhash with a per-table random seed, so no code
//! can come to depend on iteration order.

#![allow(clippy::disallowed_types)]

pub(crate) use foldhash::fast::RandomState;

pub(crate) type HashMap<K, V> = std::collections::HashMap<K, V, RandomState>;
pub(crate) type HashSet<T> = std::collections::HashSet<T, RandomState>;

#[cfg(test)]
#[path = "fast_hash_test.rs"]
mod tests;
