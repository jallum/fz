use std::collections::HashMap;

use crate::type_expr::ResolvedSpecDecl;

use super::contract::ContractArrow;
use super::{CallableValueKind, ClosureTarget, FunctionContract, TypeVarId, Types};

#[test]
fn function_contract_application_refines_callable_params_from_outer_bindings() {
    let mut types = Types::new();
    let t = types.type_var(TypeVarId(0));
    let nil = types.nil();
    let resolved = ResolvedSpecDecl {
        params: vec![t, types.arrow(&[t], nil)],
        result: types.resource(t),
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let actual_payload = types.int();
    let actual_callable = types.fn_ref_lit(ClosureTarget(17), 1);
    let applied = contract.apply(&mut types, &[actual_payload, actual_callable]);

    assert_eq!(applied.matched_arrows.len(), 1, "the contract should match one arrow");
    let matched = &applied.matched_arrows[0];
    let matched_callable = types
        .callable_clauses(&matched[1])
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
    let refined_callable = types.intersect(actual_callable, matched[1]);
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
    let resolved = ResolvedSpecDecl {
        params: vec![types.list(elem), acc, types.arrow(&[elem, acc], acc)],
        result: acc,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

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
        .callable_clauses(&applied.matched_arrows[0][2])
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

    let refined_callable = types.intersect(actual_callable, applied.matched_arrows[0][2]);
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
fn function_contract_application_binds_tagged_halt_payload_separately_from_continue_accumulator() {
    let mut types = Types::new();
    let cont_acc = types.type_var(TypeVarId(0));
    let halt_acc = types.type_var(TypeVarId(1));
    let atom_cont = types.atom_lit("cont");
    let atom_halt = types.atom_lit("halt");
    let atom_done = types.atom_lit("done");
    let atom_halted = types.atom_lit("halted");
    let cont_state = types.tuple(&[atom_cont, cont_acc]);
    let halt_state = types.tuple(&[atom_halt, halt_acc]);
    let state = types.union(cont_state, halt_state);
    let done = types.tuple(&[atom_done, cont_acc]);
    let halted = types.tuple(&[atom_halted, halt_acc]);
    let result = types.union(done, halted);
    let resolved = ResolvedSpecDecl {
        params: vec![state],
        result,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let none = types.atom_lit("none");
    let int = types.int();
    let observed_cont = types.tuple(&[atom_cont, none]);
    let observed_halt = types.tuple(&[atom_halt, int]);
    let observed_state = types.union(observed_cont, observed_halt);

    let applied = contract.apply(&mut types, &[observed_state]);
    let result = applied
        .result
        .expect("tagged union should ground both payload variables");
    let expected_done = types.tuple(&[atom_done, none]);
    let expected_halted = types.tuple(&[atom_halted, int]);
    assert!(
        types.is_subtype(&expected_done, &result),
        "continue payload should bind only the continue result arm: {}",
        types.display(&result),
    );
    assert!(
        types.is_subtype(&expected_halted, &result),
        "halt payload should bind the halted result arm separately from continue: {}",
        types.display(&result),
    );
}

#[test]
fn function_contract_application_binds_reduce_halt_payload_from_callable_return() {
    let mut types = Types::new();
    let elem = types.type_var(TypeVarId(0));
    let cont_acc = types.type_var(TypeVarId(1));
    let halt_acc = types.type_var(TypeVarId(2));
    let atom_cont = types.atom_lit("cont");
    let atom_halt = types.atom_lit("halt");
    let atom_suspend = types.atom_lit("suspend");
    let atom_done = types.atom_lit("done");
    let atom_halted = types.atom_lit("halted");
    let atom_suspended = types.atom_lit("suspended");
    let cont_state = types.tuple(&[atom_cont, cont_acc]);
    let halt_state = types.tuple(&[atom_halt, halt_acc]);
    let suspend_state = types.tuple(&[atom_suspend, cont_acc]);
    let two_states = types.union(cont_state, halt_state);
    let reducer_result = types.union(two_states, suspend_state);
    let done = types.tuple(&[atom_done, cont_acc]);
    let halted = types.tuple(&[atom_halted, halt_acc]);
    let suspended = types.tuple(&[atom_suspended, cont_acc]);
    let two_results = types.union(done, halted);
    let result = types.union(two_results, suspended);
    let reducer = types.arrow(&[elem, cont_acc], reducer_result);
    let resolved = ResolvedSpecDecl {
        params: vec![types.list(elem), reducer_result, reducer],
        result,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let int = types.int();
    let none = types.atom_lit("none");
    let actual_list = types.list(int);
    let actual_state = types.tuple(&[atom_cont, none]);
    let actual_cont = types.tuple(&[atom_cont, none]);
    let actual_halt = types.tuple(&[atom_halt, int]);
    let actual_reducer_result = types.union(actual_cont, actual_halt);
    let actual_reducer = types.arrow(&[int, none], actual_reducer_result);

    let applied = contract.apply(&mut types, &[actual_list, actual_state, actual_reducer]);
    let matched_reducer = types
        .callable_clauses(&applied.matched_arrows[0][2])
        .expect("matched reducer callable")
        .into_iter()
        .next()
        .expect("matched reducer callable clause");
    let expected_halt = types.tuple(&[atom_halt, int]);
    assert!(
        types.is_subtype(&expected_halt, &matched_reducer.ret),
        "the reducer surface should keep halt payloads independent of the continue accumulator: {}",
        types.display(&matched_reducer.ret),
    );
    let expected_halted = types.tuple(&[atom_halted, int]);
    let result = applied
        .result
        .expect("callable halt payload should ground the contract result");
    assert!(
        types.is_subtype(&expected_halted, &result),
        "the function result should carry the callable's halt payload: {}",
        types.display(&result),
    );
}

#[test]
fn function_contract_application_keeps_reduce_halt_payload_free_until_callable_return_is_known() {
    let mut types = Types::new();
    let elem = types.type_var(TypeVarId(0));
    let cont_acc = types.type_var(TypeVarId(1));
    let halt_acc = types.type_var(TypeVarId(2));
    let atom_cont = types.atom_lit("cont");
    let atom_halt = types.atom_lit("halt");
    let atom_suspend = types.atom_lit("suspend");
    let atom_done = types.atom_lit("done");
    let atom_halted = types.atom_lit("halted");
    let atom_suspended = types.atom_lit("suspended");
    let cont_state = types.tuple(&[atom_cont, cont_acc]);
    let halt_state = types.tuple(&[atom_halt, halt_acc]);
    let suspend_state = types.tuple(&[atom_suspend, cont_acc]);
    let two_states = types.union(cont_state, halt_state);
    let reducer_result = types.union(two_states, suspend_state);
    let done = types.tuple(&[atom_done, cont_acc]);
    let halted = types.tuple(&[atom_halted, halt_acc]);
    let suspended = types.tuple(&[atom_suspended, cont_acc]);
    let two_results = types.union(done, halted);
    let result = types.union(two_results, suspended);
    let reducer = types.arrow(&[elem, cont_acc], reducer_result);
    let resolved = ResolvedSpecDecl {
        params: vec![types.list(elem), reducer_result, reducer],
        result,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let int = types.int();
    let none = types.atom_lit("none");
    let actual_list = types.list(int);
    let actual_state = types.tuple(&[atom_cont, none]);
    let actual_reducer_return = types.type_var(TypeVarId(99));
    let actual_reducer = types.arrow(&[int, none], actual_reducer_return);

    let applied = contract.apply(&mut types, &[actual_list, actual_state, actual_reducer]);
    let matched_reducer = types
        .callable_clauses(&applied.matched_arrows[0][2])
        .expect("matched reducer callable")
        .into_iter()
        .next()
        .expect("matched reducer callable clause");
    let any = types.any();
    let halt_probe = types.tuple(&[atom_halt, any]);
    let halt_surface = types.intersect(matched_reducer.ret, halt_probe);
    let halt_payload = types.tuple_field_type(&halt_surface, 1);
    assert!(
        types.has_vars(&halt_payload),
        "the independent halt payload must stay free until callable return evidence arrives; ret={} payload={}",
        types.display(&matched_reducer.ret),
        types.display(&halt_payload),
    );
}

#[test]
fn addressed_function_contract_keeps_reduce_halt_payload_free_until_callable_return_is_known() {
    let mut types = Types::new();
    let elem = types.type_var(TypeVarId(0));
    let cont_acc = types.type_var(TypeVarId(1));
    let halt_acc = types.type_var(TypeVarId(2));
    let atom_cont = types.atom_lit("cont");
    let atom_halt = types.atom_lit("halt");
    let atom_suspend = types.atom_lit("suspend");
    let atom_done = types.atom_lit("done");
    let atom_halted = types.atom_lit("halted");
    let atom_suspended = types.atom_lit("suspended");
    let cont_state = types.tuple(&[atom_cont, cont_acc]);
    let halt_state = types.tuple(&[atom_halt, halt_acc]);
    let suspend_state = types.tuple(&[atom_suspend, cont_acc]);
    let two_states = types.union(cont_state, halt_state);
    let reducer_result = types.union(two_states, suspend_state);
    let done = types.tuple(&[atom_done, cont_acc]);
    let halted = types.tuple(&[atom_halted, halt_acc]);
    let suspended = types.tuple(&[atom_suspended, cont_acc]);
    let two_results = types.union(done, halted);
    let result = types.union(two_results, suspended);
    let reducer = types.arrow(&[elem, cont_acc], reducer_result);
    let list = types.list(elem);
    let params = vec![list, reducer_result, reducer];
    let arrow = types.address_arrow(&params, result);
    let contract = FunctionContract {
        arrows: vec![ContractArrow {
            arrow,
            bounds: HashMap::new(),
        }],
    };

    let int = types.int();
    let none = types.atom_lit("none");
    let actual_list = types.list(int);
    let actual_state = types.tuple(&[atom_cont, none]);
    let actual_reducer_return = types.type_var(TypeVarId(99));
    let actual_reducer = types.arrow(&[int, none], actual_reducer_return);

    let applied = contract.apply(&mut types, &[actual_list, actual_state, actual_reducer]);
    assert_eq!(
        applied.matched_arrows.len(),
        1,
        "the addressed reduce-style contract should match the concrete call"
    );
    let matched_reducer = types
        .callable_clauses(&applied.matched_arrows[0][2])
        .expect("matched reducer callable")
        .into_iter()
        .next()
        .expect("matched reducer callable clause");
    let any = types.any();
    let halt_probe = types.tuple(&[atom_halt, any]);
    let halt_surface = types.intersect(matched_reducer.ret, halt_probe);
    let halt_payload = types.tuple_field_type(&halt_surface, 1);
    assert!(
        types.has_vars(&halt_payload),
        "the addressed independent halt payload must stay free until callable return evidence arrives; ret={} payload={}",
        types.display(&matched_reducer.ret),
        types.display(&halt_payload),
    );
}

#[test]
fn function_contract_application_treats_empty_list_witness_as_underconstrained() {
    let mut types = Types::new();
    let elem = types.type_var(TypeVarId(0));
    let acc = types.type_var(TypeVarId(1));
    let resolved = ResolvedSpecDecl {
        params: vec![types.list(elem), acc, types.arrow(&[elem, acc], acc)],
        result: acc,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

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
        .callable_clauses(&applied.matched_arrows[0][2])
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
    let resolved = ResolvedSpecDecl {
        params: vec![types.arrow(&[t], t)],
        result: t,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let actual_callable = types.fn_ref_lit(ClosureTarget(29), 1);
    let applied = contract.apply(&mut types, &[actual_callable]);

    assert_eq!(applied.matched_arrows.len(), 1, "the callable surface still matches");
    assert!(
        applied.result.is_none(),
        "an underconstrained callable match should refine inputs but must not publish a raw type variable as result evidence"
    );
}

#[test]
fn function_contract_application_does_not_recurse_through_concrete_any_inputs() {
    let mut types = Types::new();
    let any = types.any();
    let resolved = ResolvedSpecDecl {
        params: vec![any],
        result: any,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let applied = contract.apply(&mut types, &[any]);

    assert_eq!(
        applied.matched_arrows.len(),
        1,
        "the concrete any contract should still match"
    );
    assert!(
        applied
            .result
            .as_ref()
            .is_some_and(|result| types.is_equivalent(result, &any)),
        "the result should stay any without recursively re-walking top list structure",
    );
}
