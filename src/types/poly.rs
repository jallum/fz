use std::fmt;

/// Parametric type-variable identifier. Vars are nominal placeholders
/// distinguished only by id; they are substituted at instantiation sites.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVarId(pub u32);

impl TypeVarId {
    /// Allocate a fresh id from the process-global counter. Tests that need
    /// stable ids should construct `TypeVarId(n)` directly rather than calling
    /// `fresh()`.
    #[allow(dead_code)]
    pub(crate) fn fresh() -> Self {
        use std::sync::atomic::{AtomicU32, Ordering};
        static NEXT: AtomicU32 = AtomicU32::new(0);
        TypeVarId(NEXT.fetch_add(1, Ordering::Relaxed))
    }
}

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
