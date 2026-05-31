//! Type specialization — the inference engine
//! (`.agent/docs/type-specialization.md`).
//!
//! Built off to the side; the planner is transplanted onto it in fz-g58.65.6.
//! A closure is modeled as a function whose first parameters are its captures,
//! bound at creation to known-typed values — so applying a closure is just a
//! call to its body function with the captures prepended as leading arguments.

use crate::fz_ir::FnId;
use crate::types::{ClosureTypes, Ty, Types};

/// The call contract for applying a closure value to `arg_tys`: its body
/// function plus the full input vector `captures ++ args`.
///
/// Captures lead because lowering splices a closure's captured slots ahead of
/// its call arguments. The captures come straight from the closure value's
/// type, so a captured closure is carried at its own concrete type — a nested
/// closure is a concrete capture, not a placeholder. `None` when `closure_ty`
/// is not a single known closure (a union of targets is resolved later).
//
// The specialization worklist (the production caller) lands in fz-g58.65.4.
#[allow(dead_code)]
pub(crate) fn closure_apply_contract<T: Types<Ty = Ty> + ClosureTypes>(
    t: &T,
    closure_ty: &Ty,
    arg_tys: &[Ty],
) -> Option<(FnId, Vec<Ty>)> {
    let info = t.closure_lit_parts(closure_ty)?;
    let mut inputs = info.captures;
    inputs.extend_from_slice(arg_tys);
    Some((info.target.into(), inputs))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{ClosureTarget, ConcreteTypes};

    #[test]
    fn closure_apply_prepends_captures_as_leading_params() {
        // A closure over fn7 capturing one int, applied to (int, int), is a call
        // to fn7 with inputs [int] ++ [int, int].
        let mut t = ConcreteTypes;
        let cap = t.int();
        let clo = t.closure_lit(ClosureTarget(7), vec![cap], 2);
        let a = t.int();
        let b = t.int();
        let (target, inputs) =
            closure_apply_contract(&t, &clo, &[a, b]).expect("singleton closure");
        assert_eq!(target, FnId(7));
        assert_eq!(inputs.len(), 3, "captures ++ args");
    }

    #[test]
    fn captured_closure_is_carried_concretely() {
        // W captures U. Applying W must surface U as a concrete leading input —
        // the nested-closure case the old planner could not settle.
        let mut t = ConcreteTypes;
        let inner = t.closure_lit(ClosureTarget(9), vec![], 2);
        let outer = t.closure_lit(ClosureTarget(8), vec![inner], 2);
        let a = t.int();
        let b = t.int();
        let (target, inputs) =
            closure_apply_contract(&t, &outer, &[a, b]).expect("singleton closure");
        assert_eq!(target, FnId(8));
        let captured = t
            .closure_lit_parts(&inputs[0])
            .expect("leading input is the captured closure, concrete");
        assert_eq!(FnId::from(captured.target), FnId(9));
    }

    #[test]
    fn non_closure_has_no_apply_contract() {
        let mut t = ConcreteTypes;
        let int = t.int();
        assert!(closure_apply_contract(&t, &int, &[]).is_none());
    }
}
