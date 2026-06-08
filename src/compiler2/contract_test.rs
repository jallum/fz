use std::collections::HashMap;

use super::contract::ContractArrow;
use super::{CallableValueKind, ClosureTarget, FunctionContract, TypeVarId, Types};

#[test]
fn function_contract_application_refines_callable_params_from_outer_bindings() {
    let mut types = Types::new();
    let t = types.type_var(TypeVarId(0));
    let nil = types.nil();
    let contract = FunctionContract {
        arrows: vec![ContractArrow {
            params: vec![t, types.arrow(&[t], nil)],
            result: types.resource(t),
            constraints: HashMap::new(),
        }],
    };

    let actual_payload = types.int();
    let actual_callable = types.fn_ref_lit(ClosureTarget(17), 1);
    let applied = contract.apply(&mut types, &[actual_payload, actual_callable]);

    assert_eq!(applied.matched_arrows.len(), 1, "the contract should match one arrow");
    let matched = &applied.matched_arrows[0];
    let matched_callable = types
        .callable_clauses(&matched.params[1])
        .expect("matched contract callable surface")
        .into_iter()
        .next()
        .expect("matched contract callable clause");
    assert!(
        types.is_integer(&matched_callable.args[0]),
        "the matched contract callable arg should inherit the payload binding",
    );
    assert!(
        types
            .resource_payload_type(applied.result.as_ref().expect("contract result"))
            .is_some_and(|payload| types.is_integer(&payload)),
        "the result should refine to resource(integer)",
    );
    let refined_callable = types.intersect(actual_callable, matched.params[1]);
    let callable = types
        .callable_value_clauses(&refined_callable)
        .expect("matched callable value surface")
        .into_iter()
        .next()
        .expect("matched callable value clause");
    assert!(
        types.is_integer(&callable.args[0]),
        "the callable arg slot should inherit the payload binding from the outer contract: {}",
        types.display(&callable.args[0]),
    );
    assert!(
        types.is_nil(&callable.ret),
        "the callable result should stay at the declared nil surface",
    );
    let closure = callable.closure.expect("closure identity should survive refinement");
    assert_eq!(closure.target, ClosureTarget(17));
    assert_eq!(closure.kind, CallableValueKind::FnRef);
}
