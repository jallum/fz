use crate::types::ClosureTypes;

/// Marker trait, blanket-implemented for every [`ClosureTypes`]. It once
/// carried the literal-fold helpers (`is_literal`, `scalar_literal`,
/// `match_literal_ty`, …) the compile-time reducer consumed; those were
/// removed with the reducer. The trait survives only as a bound alias so
/// the signatures that named it stay unchanged.
pub trait LiteralTypes: ClosureTypes {}

impl<T: ClosureTypes> LiteralTypes for T {}
