//! A single ground literal value, shared by every subsystem that needs to
//! name one concrete runtime constant: map keys, lowered-body literals,
//! dispatch-matrix constants, and runtime-observed membership sets.
//!
//! This is a crate leaf: it depends on nothing else in the crate, so
//! `types`, `fz_ir`, `dispatch_matrix`, and `runtime_type_predicate` can all
//! depend on it without deepening the existing `types <-> fz_ir` cycle.
//!
//! `GroundValue` is a lossless superset of the carriers it will eventually
//! replace. Four distinctions are load-bearing and must never be collapsed:
//! floats are IEEE-754 bits (not `f64`, so the type can derive `Eq`/`Hash`/
//! `Ord` and codegen float dispatch stays bit-exact); `Nil` and `EmptyList`
//! are different runtime `ValueKind` tags; `Binary` and `Utf8Binary` are
//! raw pre-brand bytes versus UTF-8-asserted bytes; and `Bool` is its own
//! variant, never `Atom("true")`/`Atom("false")`.
// The derived `Ord`/`PartialOrd` is bit-pattern order over the `Float(u64)`
// bits, NOT numeric order: negative floats and NaN sort by their raw bits.
// It is a stable total order suitable for map/set key ordering only; never
// use it to sort ground values by numeric magnitude.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum GroundValue {
    Int(i64),
    Float(u64),
    Atom(String),
    Bool(bool),
    Nil,
    EmptyList,
    Binary(Vec<u8>),
    Utf8Binary(Vec<u8>),
}

impl GroundValue {
    pub fn from_f64(value: f64) -> Self {
        GroundValue::Float(value.to_bits())
    }

    pub fn as_f64(&self) -> Option<f64> {
        match self {
            GroundValue::Float(bits) => Some(f64::from_bits(*bits)),
            _ => None,
        }
    }

    /// Projects onto the `{Atom, Int}` shape that map keys need, or `None`
    /// for every other ground value.
    pub fn as_map_key(&self) -> Option<MapKeyProjection> {
        match self {
            GroundValue::Atom(name) => Some(MapKeyProjection::Atom(name.clone())),
            GroundValue::Int(value) => Some(MapKeyProjection::Int(*value)),
            _ => None,
        }
    }
}

/// The atom/int projection of a [`GroundValue`] that map keys need. Kept
/// separate from `crate::types::map::MapKey` so this leaf module stays
/// dependency-free; later migrations can convert between the two.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MapKeyProjection {
    Atom(String),
    Int(i64),
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn hash_of(value: &GroundValue) -> u64 {
        let mut hasher = DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    }

    /// Float round-trips through `from_f64`/`as_f64` bit-exact, and the
    /// bit representation (not any derived float comparison) is what backs
    /// Hash/Ord -- this is why the variant stores u64 bits rather than f64.
    #[test]
    fn float_round_trips_bit_exact_and_supports_hash_and_ord() {
        let value = GroundValue::from_f64(3.5);
        assert_eq!(value.as_f64(), Some(3.5));
        assert_eq!(value, GroundValue::Float(3.5_f64.to_bits()));

        let nan = GroundValue::from_f64(f64::NAN);
        assert_eq!(nan.as_f64().unwrap().to_bits(), f64::NAN.to_bits());
        // f64::NAN != f64::NAN under IEEE-754, but GroundValue equality is
        // bit-exact, so the same NaN bit pattern compares equal to itself
        // and hashes consistently -- this is only true because Float holds
        // bits, not a raw f64.
        assert_eq!(nan, nan.clone());
        assert_eq!(hash_of(&nan), hash_of(&nan.clone()));

        let low = GroundValue::from_f64(1.0);
        let high = GroundValue::from_f64(2.0);
        assert!(low < high);
    }

    /// `Nil` and `EmptyList` are distinct runtime tags (atom vs. list) and
    /// must never be merged into a single "empty-ish" variant.
    #[test]
    fn nil_and_empty_list_are_distinct() {
        assert_ne!(GroundValue::Nil, GroundValue::EmptyList);
    }

    /// `Binary` (raw pre-brand bytes) and `Utf8Binary` (UTF-8-asserted
    /// bytes) carry the same bytes but different brand guarantees, so
    /// they must remain separate variants even when the byte content
    /// matches.
    #[test]
    fn binary_and_utf8_binary_are_distinct_despite_same_bytes() {
        let bytes = vec![104, 105];
        assert_ne!(GroundValue::Binary(bytes.clone()), GroundValue::Utf8Binary(bytes));
    }

    /// `Bool` is its own variant, not sugar over `Atom("true")`/
    /// `Atom("false")`.
    #[test]
    fn bool_is_not_an_atom() {
        assert_ne!(GroundValue::Bool(true), GroundValue::Atom("true".to_string()));
        assert_ne!(GroundValue::Bool(false), GroundValue::Atom("false".to_string()));
    }

    #[test]
    fn as_map_key_projects_atom_and_int_only() {
        assert_eq!(
            GroundValue::Atom("ok".to_string()).as_map_key(),
            Some(MapKeyProjection::Atom("ok".to_string()))
        );
        assert_eq!(GroundValue::Int(7).as_map_key(), Some(MapKeyProjection::Int(7)));
        assert_eq!(GroundValue::Nil.as_map_key(), None);
        assert_eq!(GroundValue::EmptyList.as_map_key(), None);
        assert_eq!(GroundValue::Bool(true).as_map_key(), None);
        assert_eq!(GroundValue::Binary(vec![1]).as_map_key(), None);
        assert_eq!(GroundValue::Utf8Binary(vec![1]).as_map_key(), None);
        assert_eq!(GroundValue::Float(0).as_map_key(), None);
    }
}
