use std::fmt;

/// Parametric type-variable identifier. Vars are nominal placeholders
/// distinguished only by id; they are substituted at instantiation sites.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVarId(pub u32);

impl fmt::Debug for TypeVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "α{}", self.0)
    }
}

impl fmt::Display for TypeVarId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "α{}", self.0)
    }
}
