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

/// Every non-atom/int ground value is dropped from map-key position
/// rather than coerced -- the map lattice only ever reasons about the
/// atom/int subset, so `Nil`, `Bool`, `Binary`, `Utf8Binary`, and
/// `Float` must all narrow to `None` here, exactly as `literal_map_key`
/// (compiler2/jobs/semantic.rs) drops the equivalent non-atom/int
/// literals during lowering.
#[test]
fn as_map_key_projects_atom_and_int_only() {
    assert_eq!(
        GroundValue::Atom("ok".to_string()).as_map_key(),
        Some(MapKey::Atom("ok".to_string()))
    );
    assert_eq!(GroundValue::Int(7).as_map_key(), Some(MapKey::Int(7)));
    assert_eq!(GroundValue::Nil.as_map_key(), None);
    assert_eq!(GroundValue::Bool(true).as_map_key(), None);
    assert_eq!(GroundValue::Binary(vec![1]).as_map_key(), None);
    assert_eq!(GroundValue::Utf8Binary(vec![1]).as_map_key(), None);
    assert_eq!(GroundValue::Float(0).as_map_key(), None);
}

/// The six in-subset variants all narrow to their `BodyLiteral`
/// counterpart; `Utf8Binary` is the only variant a lowered body never
/// produces, so it -- and only it -- narrows to `None`.
#[test]
fn as_body_literal_projects_the_six_lowering_variants() {
    assert_eq!(GroundValue::Int(7).as_body_literal(), Some(BodyLiteral::Int(7)));
    assert_eq!(GroundValue::Float(0).as_body_literal(), Some(BodyLiteral::Float(0)));
    assert_eq!(
        GroundValue::Atom("ok".to_string()).as_body_literal(),
        Some(BodyLiteral::Atom("ok"))
    );
    assert_eq!(GroundValue::Bool(true).as_body_literal(), Some(BodyLiteral::Bool(true)));
    assert_eq!(GroundValue::Nil.as_body_literal(), Some(BodyLiteral::Nil));
    assert_eq!(
        GroundValue::Binary(vec![1, 2]).as_body_literal(),
        Some(BodyLiteral::Binary(&[1, 2]))
    );
    assert_eq!(GroundValue::Utf8Binary(vec![1]).as_body_literal(), None);
}

/// The six in-subset variants all narrow to their `DispatchShape`
/// counterpart; raw `Binary` is the only variant the dispatch matrix
/// never constructs, so it -- and only it -- narrows to `None`.
#[test]
fn as_dispatch_shape_projects_the_six_dispatch_matrix_variants() {
    assert_eq!(GroundValue::Int(7).as_dispatch_shape(), Some(DispatchShape::Int(7)));
    assert_eq!(GroundValue::Float(0).as_dispatch_shape(), Some(DispatchShape::Float(0)));
    assert_eq!(
        GroundValue::Atom("ok".to_string()).as_dispatch_shape(),
        Some(DispatchShape::Atom("ok"))
    );
    assert_eq!(
        GroundValue::Bool(true).as_dispatch_shape(),
        Some(DispatchShape::Bool(true))
    );
    assert_eq!(GroundValue::Nil.as_dispatch_shape(), Some(DispatchShape::Nil));
    assert_eq!(
        GroundValue::Utf8Binary(vec![1, 2]).as_dispatch_shape(),
        Some(DispatchShape::Utf8Binary(&[1, 2]))
    );
    assert_eq!(GroundValue::Binary(vec![1]).as_dispatch_shape(), None);
}
