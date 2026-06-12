//! Basic-type bitmap (`BasicBits`) and bit-pattern float wrapper (`F64Bits`).

use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub(crate) struct BasicBits(pub(super) u32);

impl BasicBits {
    // Kinds without value-level distinctions. Numbers live here as plain
    // presence bits — the lattice cannot express a numeric singleton, by
    // design (Elixir's Module.Types.Descr draws the same line; constants
    // are VALUES the matcher compares at runtime). Atoms keep their
    // finite/cofinite literal-set axis; nil/bool live there too (fz-yan.2).
    pub const BINARY: BasicBits = BasicBits(1 << 0);
    pub const INT: BasicBits = BasicBits(1 << 1);
    pub const FLOAT: BasicBits = BasicBits(1 << 2);

    pub const NONE: BasicBits = BasicBits(0);
    pub const ALL: BasicBits = BasicBits((1 << 3) - 1);
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

pub(crate) const BASIC_NAMES: &[(BasicBits, &str)] = &[
    (BasicBits::INT, "int"),
    (BasicBits::FLOAT, "float"),
    (BasicBits::BINARY, "binary"),
];

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
