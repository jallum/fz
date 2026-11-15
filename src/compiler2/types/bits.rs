//! Basic-type bitmap (`BasicBits`) and bit-pattern float wrapper (`F64Bits`).

use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub(crate) struct BasicBits(pub(super) u32);

impl BasicBits {
    // Kinds without value-level distinctions. Numbers live here as plain
    // presence bits — the lattice cannot express a numeric singleton, by
    // design (Elixir's Module.Types.Descr draws the same line; constants
    // are VALUES the matcher compares at runtime). Atoms keep their
    // finite/cofinite literal-set axis; nil/bool live there too (fz-yan.2).
    // A bitstring whose bit length is a multiple of 8 is a binary; one whose
    // bit length is not is `bitstring and not binary`. The union of the two
    // is `bitstring` (Elixir's Module.Types.Descr draws the same line).
    pub const BINARY: BasicBits = BasicBits(1 << 0);
    pub const BITSTRING_NO_BINARY: BasicBits = BasicBits(1 << 3);
    pub const BITSTRING: BasicBits = BasicBits(Self::BINARY.0 | Self::BITSTRING_NO_BINARY.0);
    pub const INT: BasicBits = BasicBits(1 << 1);
    pub const FLOAT: BasicBits = BasicBits(1 << 2);

    pub const NONE: BasicBits = BasicBits(0);
    pub const ALL: BasicBits = BasicBits((1 << 4) - 1);
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

/// Widest name first: a set holding both bitstring bits prints as the one
/// word `bitstring`, and a name is spent once it prints.
pub(crate) const BASIC_NAMES: &[(BasicBits, &str)] = &[
    (BasicBits::INT, "int"),
    (BasicBits::FLOAT, "float"),
    (BasicBits::BITSTRING, "bitstring"),
    (BasicBits::BINARY, "binary"),
    (BasicBits::BITSTRING_NO_BINARY, "bitstring and not binary"),
];

/// The names a basic-bit set prints as, each bit named once.
pub(crate) fn basic_names(basic: BasicBits) -> Vec<&'static str> {
    let mut left = basic;
    let mut names = Vec::new();
    for (bit, name) in BASIC_NAMES {
        if left.contains_all(*bit) {
            names.push(*name);
            left = BasicBits(left.0 & !bit.0);
        }
    }
    names
}

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
