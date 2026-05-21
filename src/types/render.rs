use crate::types::Types;

pub trait RenderTypes: Types {
    /// Render `a` for user-facing diagnostics. Owned-string return
    /// day-one; consumers `format!("{}", t.display(&ty))`-style.
    fn display(&self, a: &Self::Ty) -> String;

    /// Length-bounded rendering for diagnostic notes. Caps each
    /// literal-set axis at a small fixed count so a huge union
    /// (`int_lit(1) | ... | int_lit(N)`) doesn't crowd a `= note:`
    /// line. Distinct from `display()`, which is exact (used by
    /// golden tests).
    fn display_for_diag(&self, a: &Self::Ty) -> String;
}
