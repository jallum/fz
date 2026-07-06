//! Primitive aliases over the shared finite-or-cofinite [`FiniteSet`].

use crate::finite_set::FiniteSet;
use crate::fz_ir::FnId;

use super::TypeVarId;

/// Singleton-type precision for atoms (and the atom-shaped nominal axes:
/// opaques, brands, vars — see [`VarSet`]). Numbers deliberately have no
/// literal sets — numeric constants are values, not types.
pub(crate) type AtomSet = FiniteSet<String>;

/// fz-try.5 — parametric type-variable identifier. Vars are nominal placeholders
/// distinguished only by id; the lattice cannot tell them apart from opaques.
/// The difference is at use sites: opaques are fixed (the name *is* the type);
/// vars are substituted at instantiation sites (fz-try.6 onward).
///
/// Per-function scoping is handled by the planner, which renames at
/// function-typing entry to ensure alpha-equivalence across signatures; the id
/// itself carries no scope.
pub(crate) type VarSet = FiniteSet<TypeVarId>;

/// fz-try.7 — deterministic var-id allocation for a closure's surface arrow.
/// Vars in a closure's `(α₀, …, αₙ₋₁) -> β` signature are keyed by `(fn_id,
/// position)`. Arg positions occupy `0..MAX_CLOSURE_ARG_VAR`; ret occupies
/// the dedicated slot at `MAX_CLOSURE_ARG_VAR`.
///
/// Determinism is required for planner fixpoint convergence: re-typing the
/// same MakeClosure during iteration must produce the same Descr. Distinct
/// closure-handles of the same lambda share their vars by construction —
/// they are parametric over the same body.
///
/// The ret slot is dedicated (not just "one past the last arg") so that a
/// closure rendered at multiple apparent arities produces a consistent ret
/// var — e.g., the value-form `&fn14:() -> ret` and the called-form
/// `&fn14:(α₀) -> ret` share the same `ret` id rather than aliasing across
/// arg positions.
const MAX_CLOSURE_ARG_VAR: u32 = 63;
const VAR_STRIDE_PER_FN: u32 = MAX_CLOSURE_ARG_VAR + 1;
pub(crate) fn closure_var_id(fn_id: FnId, position: usize) -> TypeVarId {
    let pos = position as u32;
    assert!(
        pos < VAR_STRIDE_PER_FN,
        "closure_var_id: position {} exceeds stride ({})",
        pos,
        VAR_STRIDE_PER_FN,
    );
    let id = fn_id.0 * VAR_STRIDE_PER_FN + pos;
    // A closure-surface var is a FREE var: it must stay in the untagged half of
    // the id space so display never mistakes it for a structural address. The
    // top bit is reserved for addresses (`addressed::ADDRESS_TAG`); reaching it
    // would also overflow the `fn_id * 64` stride this allocator already assumes
    // fits a `u32`.
    debug_assert!(
        id < super::addressed::ADDRESS_TAG,
        "closure-var id collided with the address tag bit"
    );
    TypeVarId(id)
}

/// fz-try.7 — the dedicated return-var slot for a closure's surface arrow.
/// Reserved at position `MAX_CLOSURE_ARG_VAR` so it does not alias arg
/// positions when the same closure is rendered at different apparent
/// arities (value-form vs called-form).
pub(crate) fn closure_ret_var_id(fn_id: FnId) -> TypeVarId {
    TypeVarId(fn_id.0 * VAR_STRIDE_PER_FN + MAX_CLOSURE_ARG_VAR)
}

/// The structural position a closure-surface var addresses within its owner's
/// arrow: an argument slot, or the dedicated return slot.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClosureSurfacePos {
    Arg(u32),
    Ret,
}

/// Invert [`closure_var_id`]/[`closure_ret_var_id`]: recover the owning `FnId`
/// and structural position packed into a free var id. Returns `None` for a
/// structural address (its tag is set, so it is not a closure-surface free var
/// and never uses this `fn_id * 64 + pos` encoding).
///
/// This is the decode half of the closure-var encoding, kept beside the encode
/// half so the stride is defined in exactly one place. It does not by itself
/// prove the id *is* a closure-surface var — a resolver encounter var or
/// typedef param also lives in the untagged space — so callers gate the result
/// against the owner's real arity before trusting the decode.
#[cfg(test)]
pub(crate) fn decode_closure_surface_var(id: TypeVarId) -> Option<(FnId, ClosureSurfacePos)> {
    if id.0 & super::addressed::ADDRESS_TAG != 0 {
        return None;
    }
    let fn_id = FnId(id.0 / VAR_STRIDE_PER_FN);
    let pos = id.0 % VAR_STRIDE_PER_FN;
    let position = if pos == MAX_CLOSURE_ARG_VAR {
        ClosureSurfacePos::Ret
    } else {
        ClosureSurfacePos::Arg(pos)
    };
    Some((fn_id, position))
}
