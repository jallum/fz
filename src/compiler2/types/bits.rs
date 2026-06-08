//! Basic-type bitmap (`BasicBits`) and bit-pattern float wrapper (`F64Bits`).

use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub(crate) struct BasicBits(pub(super) u32);

impl BasicBits {
    // Kinds without value-level distinctions (or where we choose not to track
    // them). int/float/str/atom moved into their own LiteralSet axes.
    // fz-yan.2 — NIL/BOOL bits removed; both live in the atoms axis now.
    pub const BINARY: BasicBits = BasicBits(1 << 0);

    pub const NONE: BasicBits = BasicBits(0);
    pub const ALL: BasicBits = BasicBits((1 << 1) - 1);
    pub const fn contains_all(self, o: BasicBits) -> bool {
        (self.0 & o.0) == o.0
    }
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Debug for BasicBits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BasicBits(0b{:b})", self.0)
    }
}

pub(crate) const BASIC_NAMES: &[(BasicBits, &str)] = &[(BasicBits::BINARY, "binary")];

// ----------------------------------------------------------------------
// BasicBits operations
// ----------------------------------------------------------------------

impl BasicBits {
    pub const fn union(self, o: BasicBits) -> BasicBits {
        BasicBits(self.0 | o.0)
    }
    pub const fn intersect(self, o: BasicBits) -> BasicBits {
        BasicBits(self.0 & o.0)
    }
    pub const fn neg(self) -> BasicBits {
        BasicBits(BasicBits::ALL.0 & !self.0)
    }
}

/// Bit-pattern wrapper around a non-NaN `f64` so we can put floats in
/// ordered/hashed sets. Two distinct bit patterns are considered distinct
/// values. `+0.0` and `-0.0` are distinct (matches IEEE bit equality but not
/// IEEE value equality — fine here, where the type system tracks values).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct F64Bits(u64);

impl F64Bits {
    pub(crate) fn new(f: f64) -> Self {
        assert!(!f.is_nan(), "F64Bits literal types do not support NaN");
        Self(f.to_bits())
    }
    pub(crate) fn get(self) -> f64 {
        f64::from_bits(self.0)
    }
}
impl fmt::Debug for F64Bits {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}
