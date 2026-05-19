//! Set-theoretic shape helpers consumed by `ir_typer`. The AST-walking
//! inference driver was retired by fz-ul4.11.24.1; the AST-shaped pattern /
//! expression orphans were pruned by fz-ul4.11.25.2. What survives:
//!
//! - tuple / list projection helpers (used by IR pattern narrowing)
//! - map field lookup / refinement
//! - widening operator for fixed-point termination (used by
//!   `ir_typer::specialize_return` per fz-ul4.11.24.7).

use crate::types::*;

// ----------------------------------------------------------------------
// Tuple / list projection helpers
// ----------------------------------------------------------------------

/// Project the i-th component of any positive tuple shape in `scrut` of
/// the given arity, intersecting same-arity sigs within a Conj (fz-dhd)
/// and unioning across Conjs. Falls back to `any` when no matching
/// tuple shape is present.
pub fn tuple_projections(scrut: &Descr, arity: usize) -> Vec<Descr> {
    for component in scrut.components() {
        if let Component::Tuples(view) = component
            && let Some(comps) = view.project_all(arity)
        {
            return comps;
        }
    }
    vec![Descr::any(); arity]
}

// ----------------------------------------------------------------------
// Map helpers
// ----------------------------------------------------------------------

/// Look up the value type for `key` across all positive map shapes in
/// `d`, following fz-dhd open-map semantics. Returns `None` if `d` has
/// no map shapes (call site decides the fallback).
pub fn map_field_lookup(d: &Descr, key: &MapKey) -> Option<Descr> {
    for component in d.components() {
        if let Component::Maps(view) = component {
            return view.lookup(key);
        }
    }
    None
}

pub fn refine_map_field(d: &Descr, key: &MapKey, vt: &Descr) -> Descr {
    d.refine_map_field(key, vt)
}

/// Joined element type across all positive list shapes in `scrut`,
/// using fz-dhd DNF semantics (intersect within a Conj, union across).
/// Falls back to `any` when no list shapes are present.
pub fn list_element_type(scrut: &Descr) -> Descr {
    for component in scrut.components() {
        if let Component::Lists(view) = component {
            return view.element_type();
        }
    }
    Descr::any()
}

// ----------------------------------------------------------------------
// Widening (for fixed-point termination)
// ----------------------------------------------------------------------

/// Widen a Descr toward the fixed point: literal-set axes widen to
/// their cofinite tops (`int_lit(42)` → `int()`); structural axes
/// preserve shape and their nested Descrs are widened recursively.
/// Atoms are intentionally not widened — they are nominal singletons.
///
/// fz-ul4.27.22.8 — closure captures widen elementwise via
/// `map_nested_descrs`; the FnId identity is preserved, so widening at
/// SCC fixpoints loses literal precision but keeps the closure-target
/// FnId for per-callsite singleton resolution post-widen.
pub fn widen(d: &Descr) -> Descr {
    d.widen_literals().map_nested_descrs(&widen)
}
