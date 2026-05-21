use std::fmt;

/// fz-try.5 — parametric type-variable identifier. Vars are nominal placeholders
/// distinguished only by id; the lattice cannot tell them apart from opaques.
/// The difference is at use sites: opaques are fixed (the name *is* the type);
/// vars are substituted at instantiation sites (fz-try.6 onward).
///
/// Fresh ids are allocated by `TypeVarId::fresh()` from a process-global atomic
/// counter. This is intentionally simple — per-function scoping is handled by
/// the typer (which renames at function-typing entry to ensure α-equivalence
/// across signatures); the id itself carries no scope.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct TypeVarId(pub u32);

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

/// Open-shape map keys are concrete singleton values.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum MapKey {
    Atom(String),
    Int(i64),
}
