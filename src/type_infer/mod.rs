//! Type specialization — the inference engine
//! (`.agent/docs/type-specialization.md`).
//!
//! Built off to the side; the planner is transplanted onto it in fz-g58.65.6.
//! A closure is modeled as a function whose first parameters are its captures,
//! bound at creation to known-typed values — so applying a closure is just a
//! call to its body function with the captures prepended as leading arguments.
//!
//! The engine is wired into the planner at fz-g58.65.6; until then only its own
//! tests exercise it, so the module is dead in non-test builds.
#![allow(dead_code)]

use crate::fz_ir::{BinOp, BlockId, Const, FnId, FnIr, Module, Prim, Stmt, Term, Var};
use crate::types::{ClosureTypes, Ty, Types};
use std::collections::HashMap;

/// The call contract for applying a closure value to `arg_tys`: its body
/// function plus the full input vector `captures ++ args`.
///
/// Captures lead because lowering splices a closure's captured slots ahead of
/// its call arguments. The captures come straight from the closure value's
/// type, so a captured closure is carried at its own concrete type — a nested
/// closure is a concrete capture, not a placeholder. `None` when `closure_ty`
/// is not a single known closure (a union of targets is resolved later).
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

/// Infer a function's return type from its body, given its input types.
///
/// Straight-line only for now — `Const`, arithmetic/comparison `BinOp`,
/// `Return`, and `Goto` chaining. Calls, branches, closures, and recursion
/// arrive with the worklist in fz-g58.65.4.2.
pub(crate) fn infer_return<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    module: &Module,
    fn_id: FnId,
    input_tys: &[Ty],
) -> Ty {
    let f = module.fn_by_id(fn_id);
    let mut env: HashMap<Var, Ty> = HashMap::new();
    for (param, ty) in f.block(f.entry).params.iter().zip(input_tys) {
        env.insert(*param, ty.clone());
    }
    infer_block(t, f, f.entry, &mut env)
}

fn infer_block<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    f: &FnIr,
    block_id: BlockId,
    env: &mut HashMap<Var, Ty>,
) -> Ty {
    let block = f.block(block_id);
    for Stmt::Let(v, prim) in &block.stmts {
        let ty = type_prim(t, prim, env);
        env.insert(*v, ty);
    }
    match &block.terminator {
        Term::Return(v) => env.get(v).cloned().unwrap_or_else(|| t.any()),
        Term::Goto(target, args) => {
            let arg_tys: Vec<Ty> = args
                .iter()
                .map(|a| env.get(a).cloned().unwrap_or_else(|| t.any()))
                .collect();
            for (param, ty) in f.block(*target).params.iter().zip(arg_tys) {
                env.insert(*param, ty);
            }
            infer_block(t, f, *target, env)
        }
        // A halt path yields no return value.
        Term::Halt(_) => t.none(),
        // Calls, branches, closures, recursion: fz-g58.65.4.2.
        _ => t.any(),
    }
}

fn type_prim<T: Types<Ty = Ty> + ClosureTypes>(
    t: &mut T,
    prim: &Prim,
    env: &HashMap<Var, Ty>,
) -> Ty {
    match prim {
        Prim::Const(c) => match c {
            Const::Int(n) => t.int_lit(*n),
            Const::Float(f) => t.float_lit(*f),
            Const::Nil => t.nil(),
            Const::True => t.bool_lit(true),
            Const::False => t.bool_lit(false),
            // Atom typing arrives with the state-machine corpus in .4.2.
            Const::Atom(_) => t.any(),
        },
        Prim::BinOp(op, a, b) => {
            let lt = env.get(a).cloned().unwrap_or_else(|| t.any());
            let rt = env.get(b).cloned().unwrap_or_else(|| t.any());
            match op {
                // Arithmetic: the result rides the operands' refinement join
                // (int ⊔ int = int). Modeling `+` as a signature lands in .4.2.
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    t.refine_widen(&lt, &rt)
                }
                _ => t.bool(),
            }
        }
        // Remaining prims (MakeClosure, list ops, …): fz-g58.65.4.2.
        _ => t.any(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{ClosureTarget, ConcreteTypes};

    /// Lower a source program to its IR `Module` — the same input the planner
    /// consumes, stopping before `plan_module` (which diverges on the corpus's
    /// nested-closure programs today).
    fn lower(src: &str) -> Module {
        let mut t = ConcreteTypes;
        let providers = crate::modules::pipeline::ProviderInputs::new(
            crate::modules::artifact_store::DEFAULT_ARTIFACT_ROOT.to_string(),
            Vec::new(),
        );
        let tel = crate::telemetry::NullTelemetry;
        crate::modules::pipeline::compile_source_with_providers(
            &mut t,
            src.to_string(),
            "spike.fz".to_string(),
            &providers,
            &tel,
        )
        .unwrap_or_else(|_| panic!("pipeline error lowering spike"))
        .unwrap_or_else(|_| panic!("frontend error lowering spike"))
        .module
    }

    #[test]
    fn add_infers_int_via_harness() {
        let mut t = ConcreteTypes;
        let module = lower(include_str!("../../spike/add.fz"));
        let add_id = module.fn_by_name("add").expect("add fn").id;
        let int = t.int();
        let ret = infer_return(&mut t, &module, add_id, &[int.clone(), int.clone()]);
        assert!(t.is_equivalent(&ret, &int), "add(int, int) should infer int");
    }

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
