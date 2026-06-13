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

#[test]
fn function_contract_application_refines_reduce_style_callable_from_list_and_accumulator_bindings() {
    let mut types = Types::new();
    let elem = types.type_var(TypeVarId(0));
    let acc = types.type_var(TypeVarId(1));
    let contract = FunctionContract {
        arrows: vec![ContractArrow {
            params: vec![types.list(elem), acc, types.arrow(&[elem, acc], acc)],
            result: acc,
            constraints: HashMap::new(),
        }],
    };

    let int = types.int();
    let actual_list = types.list(int);
    let actual_acc = types.int_lit(0);
    let actual_callable = types.fn_ref_lit(ClosureTarget(23), 2);

    let applied = contract.apply(&mut types, &[actual_list, actual_acc, actual_callable]);
    assert_eq!(
        applied.matched_arrows.len(),
        1,
        "the reduce-style contract should match one arrow"
    );

    let matched_callable = types
        .callable_clauses(&applied.matched_arrows[0].params[2])
        .expect("matched reduce callable surface")
        .into_iter()
        .next()
        .expect("matched reduce callable clause");
    assert!(
        types.is_integer(&matched_callable.args[0]),
        "the reducer element input should inherit the list element binding: {}",
        types.display(&matched_callable.args[0]),
    );
    assert_eq!(
        matched_callable.args[1], actual_acc,
        "the reducer accumulator input should inherit the concrete accumulator binding",
    );
    assert_eq!(
        matched_callable.ret, actual_acc,
        "the reducer return should inherit the concrete accumulator binding",
    );

    let refined_callable = types.intersect(actual_callable, applied.matched_arrows[0].params[2]);
    let callable = types
        .callable_value_clauses(&refined_callable)
        .expect("refined reduce callable value surface")
        .into_iter()
        .next()
        .expect("refined reduce callable clause");
    assert!(
        types.is_integer(&callable.args[0]),
        "the callable element input should stay specialized after intersect: {}",
        types.display(&callable.args[0]),
    );
    assert_eq!(callable.args[1], actual_acc);
    assert_eq!(callable.ret, actual_acc);
    let closure = callable
        .closure
        .expect("reduce-style fn ref should preserve closure identity");
    assert_eq!(closure.target, ClosureTarget(23));
    assert_eq!(closure.kind, CallableValueKind::FnRef);
}

#[test]
fn function_contract_application_treats_empty_list_witness_as_underconstrained() {
    let mut types = Types::new();
    let elem = types.type_var(TypeVarId(0));
    let acc = types.type_var(TypeVarId(1));
    let contract = FunctionContract {
        arrows: vec![ContractArrow {
            params: vec![types.list(elem), acc, types.arrow(&[elem, acc], acc)],
            result: acc,
            constraints: HashMap::new(),
        }],
    };

    let int = types.int();
    let actual_list = types.non_empty_list(int);
    let actual_acc = types.empty_list();
    let actual_callable = types.fn_ref_lit(ClosureTarget(23), 2);

    let applied = contract.apply(&mut types, &[actual_list, actual_acc, actual_callable]);

    assert_eq!(
        applied.matched_arrows.len(),
        1,
        "the reduce-style contract should still match"
    );
    assert!(
        applied.result.is_none(),
        "an empty-list accumulator witness should keep the generic result underconstrained",
    );

    let matched_callable = types
        .callable_clauses(&applied.matched_arrows[0].params[2])
        .expect("matched reduce callable surface")
        .into_iter()
        .next()
        .expect("matched reduce callable clause");
    assert!(
        types.is_integer(&matched_callable.args[0]),
        "the reducer element input should still inherit the enumerable element binding: {}",
        types.display(&matched_callable.args[0]),
    );
    assert!(
        types.has_vars(&matched_callable.args[1]),
        "an empty-list witness should keep the reducer accumulator input generic instead of collapsing it to []: {}",
        types.display(&matched_callable.args[1]),
    );
    assert!(
        types.has_vars(&matched_callable.ret),
        "an empty-list witness should keep the reducer return generic instead of collapsing it to []: {}",
        types.display(&matched_callable.ret),
    );
}

#[test]
fn function_contract_application_does_not_publish_underconstrained_result_evidence() {
    let mut types = Types::new();
    let t = types.type_var(TypeVarId(0));
    let contract = FunctionContract {
        arrows: vec![ContractArrow {
            params: vec![types.arrow(&[t], t)],
            result: t,
            constraints: HashMap::new(),
        }],
    };

    let actual_callable = types.fn_ref_lit(ClosureTarget(29), 1);
    let applied = contract.apply(&mut types, &[actual_callable]);

    assert_eq!(applied.matched_arrows.len(), 1, "the callable surface still matches");
    assert!(
        applied.result.is_none(),
        "an underconstrained callable match should refine inputs but must not publish a raw type variable as result evidence"
    );
}
