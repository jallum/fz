//! The hash tables of the compiler.
//!
//! Each table is seeded randomly when it is built, as std's tables are, so no
//! code can come to depend on iteration order. The hash function is foldhash's,
//! which costs far less per key than std's SipHash. Every table in the compiler
//! names these aliases; the lints in `clippy.toml` reject std's.

#![allow(clippy::disallowed_types)]

pub use foldhash::fast::RandomState;

pub type HashMap<K, V> = std::collections::HashMap<K, V, RandomState>;
pub type HashSet<T> = std::collections::HashSet<T, RandomState>;
pub type IndexMap<K, V> = indexmap::IndexMap<K, V, RandomState>;

#[cfg(test)]
#[path = "fast_hash_test.rs"]
mod tests;
