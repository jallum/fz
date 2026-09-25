//! A single ground literal value, shared by every subsystem that needs to
//! name one concrete runtime constant: map keys, lowered-body literals,
//! dispatch-matrix constants, and runtime-observed membership sets.
//!
//! This is a crate leaf: it depends on nothing else in the crate, so
//! `types`, `fz_ir`, `dispatch_matrix`, and `runtime_type_predicate` can all
//! depend on it without deepening the existing `types <-> fz_ir` cycle.
//!
//! `GroundValue` is a lossless superset of the carriers it will eventually
//! replace. Three distinctions are load-bearing and must never be collapsed:
//! floats are IEEE-754 bits (not `f64`, so the type can derive `Eq`/`Hash`/
//! `Ord` and codegen float dispatch stays bit-exact); `Binary` and
//! `Utf8Binary` are raw pre-brand bytes versus UTF-8-asserted bytes; and
//! `Bool` is its own variant, never `Atom("true")`/`Atom("false")`.
//!
//! `[]` (the empty list) has no variant here: source lowering never builds a
//! ground-value dispatch const for it. `Pattern::List`/`Expr::List` route
//! through the structurally distinct `Region::List(ListRegion::Empty/Cons)`
//! region (`dispatch_matrix::pattern::append_list_pattern`) instead, because
//! matching a cons cell needs head/tail projections a flat ground-value
//! equality test cannot express. `nil` (the atom) and `[]` (the empty list)
//! therefore stay distinct by construction: `Nil` is the only "nil-ish"
//! member of this enum, and nothing constructs an empty-list ground value to
//! confuse it with.
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
    pub fn as_map_key(&self) -> Option<MapKey> {
        match self {
            GroundValue::Atom(name) => Some(MapKey::Atom(name.clone())),
            GroundValue::Int(value) => Some(MapKey::Int(*value)),
            _ => None,
        }
    }

    /// Projects onto the `{Int, Float, Atom, Bool, Nil, Binary}` shape that
    /// lowered function bodies can express as a literal, or `None` for
    /// `Utf8Binary` -- lowering never produces it (brand erasure turns a
    /// dispatch-const `Utf8Binary` into a body-literal `Binary` before it
    /// reaches this projection).
    pub fn as_body_literal(&self) -> Option<BodyLiteral<'_>> {
        match self {
            GroundValue::Int(value) => Some(BodyLiteral::Int(*value)),
            GroundValue::Float(bits) => Some(BodyLiteral::Float(*bits)),
            GroundValue::Atom(name) => Some(BodyLiteral::Atom(name)),
            GroundValue::Bool(value) => Some(BodyLiteral::Bool(*value)),
            GroundValue::Nil => Some(BodyLiteral::Nil),
            GroundValue::Binary(bytes) => Some(BodyLiteral::Binary(bytes)),
            GroundValue::Utf8Binary(_) => None,
        }
    }

    /// Projects onto the `{Int, Float, Atom, Bool, Nil, Utf8Binary}` shape
    /// that the dispatch matrix constructs, or `None` for raw `Binary` --
    /// `dispatch_matrix::pattern` only ever builds `Utf8Binary` consts,
    /// never a raw `Binary`.
    pub fn as_dispatch_shape(&self) -> Option<DispatchShape<'_>> {
        match self {
            GroundValue::Int(value) => Some(DispatchShape::Int(*value)),
            GroundValue::Float(bits) => Some(DispatchShape::Float(*bits)),
            GroundValue::Atom(name) => Some(DispatchShape::Atom(name)),
            GroundValue::Bool(value) => Some(DispatchShape::Bool(*value)),
            GroundValue::Nil => Some(DispatchShape::Nil),
            GroundValue::Utf8Binary(bytes) => Some(DispatchShape::Utf8Binary(bytes)),
            GroundValue::Binary(_) => None,
        }
    }
}

/// The closed subset of [`GroundValue`] that a lowered function body can
/// express as a literal. Every consumer of a body literal matches this type
/// exhaustively instead of hand-copying an `unreachable!()` arm for the one
/// variant -- `Utf8Binary` -- that lowering never produces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BodyLiteral<'a> {
    Int(i64),
    Float(u64),
    Atom(&'a str),
    Bool(bool),
    Nil,
    Binary(&'a [u8]),
}

/// The closed subset of [`GroundValue`] that the dispatch matrix constructs.
/// Every dispatch-const consumer matches this type exhaustively instead of
/// hand-copying an `unreachable!()` arm for the one variant -- raw `Binary`
/// -- that the dispatch matrix never builds.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DispatchShape<'a> {
    Int(i64),
    Float(u64),
    Atom(&'a str),
    Bool(bool),
    Nil,
    Utf8Binary(&'a [u8]),
}

/// The atom/int projection of a [`GroundValue`] that open-shape map keys
/// need. This is the single canonical `{Atom, Int}` key shape: `crate::types`
/// re-exports it as `crate::types::MapKey` rather than defining its own, so
/// there is exactly one such enum in the crate.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MapKey {
    Atom(String),
    Int(i64),
}

#[cfg(test)]
#[path = "ground_value_test.rs"]
mod ground_value_test;
