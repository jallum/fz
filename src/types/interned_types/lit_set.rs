//! Finite-or-cofinite `LiteralSet<T>` and its primitive aliases.

use std::collections::BTreeSet;

use crate::fz_ir::FnId;
use crate::types::TypeVarId;

use super::bits::F64Bits;

/// A finite-or-cofinite set over `T`. `cofinite=false` means "exactly these";
/// `cofinite=true` means "every value of T EXCEPT these". `(false, {})` is
/// empty; `(true, {})` is the full universe of T.
///
/// Used to track singleton-type precision for atoms, ints, strs, and floats
/// (the latter via the `F64Bits` wrapper for sane equality/ordering).
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct LiteralSet<T: Ord + Clone> {
    pub set: BTreeSet<T>,
    pub cofinite: bool,
}

impl<T: Ord + Clone> LiteralSet<T> {
    pub(crate) fn none() -> Self {
        Self {
            set: BTreeSet::new(),
            cofinite: false,
        }
    }
    pub(crate) fn any() -> Self {
        Self {
            set: BTreeSet::new(),
            cofinite: true,
        }
    }
    pub(crate) fn lit(v: T) -> Self {
        let mut s = BTreeSet::new();
        s.insert(v);
        Self {
            set: s,
            cofinite: false,
        }
    }
    pub(crate) fn is_none(&self) -> bool {
        !self.cofinite && self.set.is_empty()
    }
    pub(crate) fn is_any(&self) -> bool {
        self.cofinite && self.set.is_empty()
    }
    pub(crate) fn finite(&self) -> Option<impl Iterator<Item = T> + '_> {
        (!self.cofinite).then(|| self.set.iter().cloned())
    }
    pub(crate) fn finite_len(&self) -> Option<usize> {
        (!self.cofinite).then_some(self.set.len())
    }
    pub(crate) fn union(&self, o: &Self) -> Self {
        let (a, b) = (&self.set, &o.set);
        match (self.cofinite, o.cofinite) {
            (false, false) => Self {
                set: a | b,
                cofinite: false,
            },
            (false, true) => Self {
                set: b - a,
                cofinite: true,
            },
            (true, false) => Self {
                set: a - b,
                cofinite: true,
            },
            (true, true) => Self {
                set: a & b,
                cofinite: true,
            },
        }
    }
    pub(crate) fn intersect(&self, o: &Self) -> Self {
        let (a, b) = (&self.set, &o.set);
        match (self.cofinite, o.cofinite) {
            (false, false) => Self {
                set: a & b,
                cofinite: false,
            },
            (false, true) => Self {
                set: a - b,
                cofinite: false,
            },
            (true, false) => Self {
                set: b - a,
                cofinite: false,
            },
            (true, true) => Self {
                set: a | b,
                cofinite: true,
            },
        }
    }
    pub(crate) fn neg(&self) -> Self {
        Self {
            set: self.set.clone(),
            cofinite: !self.cofinite,
        }
    }
}

pub(crate) type AtomSet = LiteralSet<String>;
pub(crate) type IntSet = LiteralSet<i64>;
pub(crate) type FloatSet = LiteralSet<F64Bits>;

/// fz-try.5 — parametric type-variable identifier. Vars are nominal placeholders
/// distinguished only by id; the lattice cannot tell them apart from opaques.
/// The difference is at use sites: opaques are fixed (the name *is* the type);
/// vars are substituted at instantiation sites (fz-try.6 onward).
///
/// Fresh ids are allocated by `TypeVarId::fresh()` from a process-global atomic
/// counter. This is intentionally simple — per-function scoping is handled by
/// the planner (which renames at function-typing entry to ensure α-equivalence
/// across signatures); the id itself carries no scope.
pub(crate) type VarSet = LiteralSet<TypeVarId>;

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
    TypeVarId(fn_id.0 * VAR_STRIDE_PER_FN + pos)
}

/// fz-try.7 — the dedicated return-var slot for a closure's surface arrow.
/// Reserved at position `MAX_CLOSURE_ARG_VAR` so it does not alias arg
/// positions when the same closure is rendered at different apparent
/// arities (value-form vs called-form).
pub(crate) fn closure_ret_var_id(fn_id: FnId) -> TypeVarId {
    TypeVarId(fn_id.0 * VAR_STRIDE_PER_FN + MAX_CLOSURE_ARG_VAR)
}
