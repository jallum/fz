use std::collections::{BTreeSet, HashMap};

use crate::diag::codes;
use crate::modules::identity::ModuleName;
use crate::telemetry::{Capture, ConfiguredTelemetry};
use crate::type_expr::ResolvedSpecDecl;

use super::contract::{ContractArrow, ResolvedContractArrow};
use super::drive_harness::metadata_str;
use super::protocol::ProtocolDomainObligation;
use super::{
    CallableValueKind, ClosureTarget, CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, FunctionContract,
    MapKey, ModuleId, RootSubmission, TypeVarId, Types,
};

/// The `Enumerable` protocol identity every domain-obligation test below
/// resolves its marker against.
fn enumerable_protocol() -> ModuleName {
    ModuleName::parse_dotted("Enumerable").expect("protocol name parses")
}

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
            protocol_domain_obligations: BTreeSet::new(),
            structural: None,
            variadic_tail: None,
        }],
        extern_wire: None,
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

/// A `[]` seed leaves a reduce-style contract with NO published result, and the
/// reason is the opaque reducer, not the `[]`.
///
/// `acc` occurs covariantly twice -- at the seed, and in the reducer arrow's
/// RESULT, which is the occurrence that says what the accumulator becomes. The
/// callable argument is a bare `fn_ref`, so that second occurrence is unreadable
/// and the join behind `acc` is partial; the clause answers `Underconstrained`
/// and `AppliedFunctionContract::result` stays `None` (fz-kdt.210).
///
/// THE PARAMETER HALF IS PINNED KNOWN-WRONG. A partial join still instantiates
/// the clause domain, so the reducer surface comes back clamped to the seed's
/// own type -- `(int, []) -> []` -- and a later rung whose accumulator has grown
/// does not fit the domain the first rung published. That is fz-kdt.216's
/// subject, and it owns the fix. Until fz-kdt.120 the fz-f98.16 empty-list veto
/// hid this shape by deleting the seed's binding outright; the veto is gone,
/// the clamp is visible here, and it moves no fixture on the corpus.
#[test]
fn function_contract_application_publishes_no_result_for_an_empty_list_seed() {
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
        "a partial join behind the accumulator must publish no result",
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
        types.is_equivalent(&matched_callable.args[1], &actual_acc),
        "KNOWN-WRONG (fz-kdt.216): the parameter surface clamps the reducer accumulator to the seed",
    );
    assert!(
        types.is_equivalent(&matched_callable.ret, &actual_acc),
        "KNOWN-WRONG (fz-kdt.216): and clamps its return to the seed with it",
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

#[test]
fn function_contract_application_reports_unsatisfied_when_no_arrow_accepts_observed_inputs() {
    let mut types = Types::new();
    let float = types.float();
    let resolved = ResolvedSpecDecl {
        params: vec![float],
        result: float,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let int = types.int();
    let applied = contract.apply(&mut types, &[int]);

    assert!(
        !applied.satisfied,
        "a concrete integer call must not satisfy a float-only contract"
    );
    assert!(
        applied.matched_arrows.is_empty(),
        "an unsatisfied contract should not refine inputs"
    );
    assert!(
        applied.result.is_none(),
        "an unsatisfied contract should not publish return evidence"
    );
}

#[test]
fn function_contract_application_tracks_enforceable_arrows_separately_from_matching_skipped_arrows() {
    let mut types = Types::new();
    let int = types.int();
    let float = types.float();
    let skipped = ResolvedSpecDecl {
        params: vec![int],
        result: int,
        constraints: HashMap::new(),
    };
    let enforced = ResolvedSpecDecl {
        params: vec![float],
        result: float,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_classified_arrows(
        &mut types,
        vec![
            ResolvedContractArrow::with_obligations(
                skipped,
                BTreeSet::from([ProtocolDomainObligation::from_protocol(enumerable_protocol())]),
            ),
            ResolvedContractArrow::with_obligations(enforced, BTreeSet::new()),
        ],
    );

    let applied = contract.apply(&mut types, &[int]);

    assert!(applied.satisfied, "the skipped arrow still contributes to refinement");
    assert!(
        applied.enforceable,
        "the contract still has an enforceable concrete arrow"
    );
    assert!(
        !applied.enforceable_satisfied,
        "a matching skipped arrow must not mask rejection by every enforceable arrow"
    );
}

#[test]
fn function_contract_arrow_stores_direct_protocol_domain_obligations() {
    let mut types = Types::new();
    let domain = types.protocol_domain_of(enumerable_protocol());
    let int = types.int();
    let resolved = ResolvedSpecDecl {
        params: vec![domain],
        result: int,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    assert_eq!(
        contract.arrows[0].protocol_domain_obligations,
        BTreeSet::from([ProtocolDomainObligation::from_protocol(enumerable_protocol())]),
        "the durable arrow should carry the resolved protocol marker"
    );
    let applied = contract.apply(&mut types, &[int]);
    assert!(
        !applied.enforceable,
        "a direct protocol-domain arrow should not participate in structural spec/violation enforcement yet"
    );
    assert!(
        applied.enforceable_satisfied,
        "without enforceable concrete arrows there is no structural violation to emit"
    );
}

#[test]
fn function_contract_mixed_protocol_and_concrete_keeps_concrete_rejection_enforceable() {
    let mut types = Types::new();
    let domain = types.protocol_domain_of(enumerable_protocol());
    let float = types.float();
    let int = types.int();
    let protocol_arrow = ResolvedSpecDecl {
        params: vec![domain],
        result: int,
        constraints: HashMap::new(),
    };
    let concrete_arrow = ResolvedSpecDecl {
        params: vec![float],
        result: float,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![protocol_arrow, concrete_arrow]);

    let applied = contract.apply(&mut types, &[int]);

    assert!(
        applied.enforceable,
        "the concrete overload remains structurally enforceable"
    );
    assert!(
        !applied.enforceable_satisfied,
        "an integer call rejected by every concrete overload must still be a structural violation"
    );
}

#[test]
fn function_contract_arrow_stores_protocol_domain_obligations_from_when_bounds() {
    let mut types = Types::new();
    let var = TypeVarId(0);
    let param = types.type_var(var);
    let int = types.int();
    let domain = types.protocol_domain_of(enumerable_protocol());
    let mut constraints = HashMap::new();
    constraints.insert(var, domain);
    let resolved = ResolvedSpecDecl {
        params: vec![param],
        result: int,
        constraints,
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    assert_eq!(
        contract.arrows[0].protocol_domain_obligations,
        BTreeSet::from([ProtocolDomainObligation::from_protocol(enumerable_protocol())]),
        "protocol markers in bounds must be classified even when the arrow surface is only a variable"
    );
}

#[test]
fn function_contract_input_domains_instantiate_top_level_bounded_union() {
    let mut types = Types::new();
    let var = TypeVarId(0);
    let param = types.type_var(var);
    let a = types.atom_lit("a");
    let b = types.atom_lit("b");
    let domain = types.union(a, b);
    let result = types.atom();
    let contract = FunctionContract::from_resolved(
        &mut types,
        vec![ResolvedSpecDecl {
            params: vec![param],
            result,
            constraints: HashMap::from([(var, domain)]),
        }],
    );

    let row = contract.arrows[0].input_domain_row(&mut types);

    assert_eq!(row.len(), 1);
    assert!(types.is_equivalent(&row[0], &domain));
}

#[test]
fn function_contract_input_domains_instantiate_nested_bounded_variable() {
    let mut types = Types::new();
    let var = TypeVarId(0);
    let nested = types.type_var(var);
    let a = types.atom_lit("a");
    let b = types.atom_lit("b");
    let domain = types.union(a, b);
    let tuple = types.tuple(&[nested]);
    let result = types.atom();
    let contract = FunctionContract::from_resolved(
        &mut types,
        vec![ResolvedSpecDecl {
            params: vec![tuple],
            result,
            constraints: HashMap::from([(var, domain)]),
        }],
    );

    let row = contract.arrows[0].input_domain_row(&mut types);
    let expected = types.tuple(&[domain]);

    assert!(types.is_equivalent(&row[0], &expected));
}

#[test]
fn function_contract_input_domains_close_dependent_bounds_without_grounding_unbounded_vars() {
    let mut types = Types::new();
    let outer = TypeVarId(0);
    let inner = TypeVarId(1);
    let outer_ty = types.type_var(outer);
    let inner_ty = types.type_var(inner);
    let a = types.atom_lit("a");
    let b = types.atom_lit("b");
    let domain = types.union(a, b);
    let result = types.atom();
    let bounded = FunctionContract::from_resolved(
        &mut types,
        vec![ResolvedSpecDecl {
            params: vec![outer_ty],
            result,
            constraints: HashMap::from([(outer, inner_ty), (inner, domain)]),
        }],
    );
    let unbounded = FunctionContract::from_resolved(
        &mut types,
        vec![ResolvedSpecDecl {
            params: vec![outer_ty],
            result,
            constraints: HashMap::new(),
        }],
    );
    let expanding = types.tuple(&[inner_ty]);
    let cyclic = FunctionContract::from_resolved(
        &mut types,
        vec![ResolvedSpecDecl {
            params: vec![outer_ty],
            result,
            constraints: HashMap::from([(outer, expanding), (inner, outer_ty)]),
        }],
    );

    let bounded_row = bounded.arrows[0].input_domain_row(&mut types);
    let unbounded_row = unbounded.arrows[0].input_domain_row(&mut types);
    let cyclic_row = cyclic.arrows[0].input_domain_row(&mut types);

    assert!(types.is_equivalent(&bounded_row[0], &domain));
    assert!(types.has_vars(&unbounded_row[0]));
    assert!(types.is_equivalent(&cyclic_row[0], &outer_ty));
}

#[test]
fn dependent_contract_bounds_are_stable_across_fresh_type_worlds() {
    for reverse in [false, true] {
        let mut types = Types::new();
        let outer = TypeVarId(0);
        let inner = TypeVarId(1);
        let outer_ty = types.type_var(outer);
        let inner_ty = types.type_var(inner);
        let a = types.atom_lit("a");
        let b = types.atom_lit("b");
        let domain = types.union(a, b);
        let mut constraints = HashMap::new();
        if reverse {
            constraints.insert(inner, domain);
            constraints.insert(outer, inner_ty);
        } else {
            constraints.insert(outer, inner_ty);
            constraints.insert(inner, domain);
        }
        let contract = FunctionContract::from_resolved(
            &mut types,
            vec![ResolvedSpecDecl {
                params: vec![outer_ty],
                result: outer_ty,
                constraints,
            }],
        );

        let applied = contract.apply(&mut types, &[a]);
        assert!(applied.satisfied);
        assert!(applied.enforceable_satisfied);
        assert!(types.is_equivalent(&applied.result.expect("dependent bound should resolve"), &a));
    }
}

#[test]
fn function_contract_ignores_protocol_markers_inside_nested_complements() {
    let mut types = Types::new();
    let any = types.any();
    let domain = types.protocol_domain_of(enumerable_protocol());
    let int = types.int();
    let tuple = types.tuple(&[domain]);
    let list = types.list(domain);
    let resource = types.resource(domain);
    let fun = types.arrow(&[domain], int);
    let map_key = MapKey::Atom("value".to_string());
    let map = types.map(&[(map_key, domain)]);
    let negated_nested_shapes = [tuple, list, resource, fun, map]
        .into_iter()
        .map(|ty| types.difference(any, ty))
        .map(|param| ResolvedSpecDecl {
            params: vec![param],
            result: int,
            constraints: HashMap::new(),
        })
        .collect::<Vec<_>>();

    let contract = FunctionContract::from_resolved(&mut types, negated_nested_shapes);

    assert!(
        contract
            .arrows
            .iter()
            .all(|arrow| arrow.protocol_domain_obligations.is_empty()),
        "markers inside nested negative clauses describe excluded values, not positive protocol-domain obligations"
    );
    let applied = contract.apply(&mut types, &[int]);
    assert!(
        applied.enforceable,
        "negative nested marker mentions must not disable structural enforcement"
    );
    assert!(
        applied.enforceable_satisfied,
        "a concrete non-nested argument should still satisfy the enforceable complement arrows"
    );
}

#[test]
fn derive_function_contract_carries_protocol_domain_obligation_through_transitive_aliases() {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    let root = compiler.submit_root(RootSubmission {
        module_name: Some("M".to_string()),
        name: "f".to_string(),
        arity: 1,
        need: ExecutableNeed::Value,
    });
    compiler.submit_code(CodeSubmission {
        name: Some("alias_protocol_domain_contract.fz".to_string()),
        text: concat!(
            "defprotocol Enumerable do\n",
            "  def reduce(enumerable, acc, reducer)\n",
            "end\n",
            "\n",
            "defmodule M do\n",
            "  @type enum_int :: Enumerable.t(integer)\n",
            "  @type alias_enum_int :: enum_int\n",
            "  @spec f(alias_enum_int) :: integer\n",
            "  def f(_), do: 1\n",
            "end\n",
        )
        .to_string(),
    });

    assert!(
        matches!(compiler.drive(), DriveOutcome::Resolved),
        "alias protocol-domain contract should settle through the normal resolver"
    );
    let function = compiler.root_function(root);
    let contract = compiler
        .world()
        .function_contract(function)
        .expect("f/1 should publish a function contract");

    assert_eq!(contract.arrows.len(), 1);
    assert_eq!(
        contract.arrows[0].protocol_domain_obligations,
        BTreeSet::from([ProtocolDomainObligation::from_protocol(enumerable_protocol())]),
        "transitive @type aliases should expand to the protocol marker before contract classification"
    );
}

#[test]
fn ground_union_input_overlapping_each_clause_satisfies_the_contract() {
    // `+/2` shape: no single arrow accepts (int | float, int), but the SET
    // {(int, int) -> int, (float, int) -> float} covers every ground member.
    // Coverage by the set is satisfaction; the result is the union of the
    // per-member results.
    let mut types = Types::new();
    let int = types.int();
    let float = types.float();
    let arrows = vec![
        ResolvedSpecDecl {
            params: vec![int, int],
            result: int,
            constraints: HashMap::new(),
        },
        ResolvedSpecDecl {
            params: vec![float, int],
            result: float,
            constraints: HashMap::new(),
        },
    ];
    let contract = FunctionContract::from_resolved(&mut types, arrows);

    let number = types.union(int, float);
    let applied = contract.apply(&mut types, &[number, int]);
    assert!(
        applied.enforceable_satisfied,
        "a ground union whose members overlap different clauses must satisfy the contract"
    );
    let expected = types.union(int, float);
    let result = applied.result.expect("the per-clause overlaps should produce a result");
    assert!(
        types.is_equivalent(&result, &expected),
        "the union's result should join the per-member results: {}",
        types.display(&result),
    );
}

#[test]
fn a_union_with_a_member_no_clause_accepts_is_answered_on_the_overlap() {
    // (:bad | int, int): the :bad member fits no clause, so at run time it meets
    // Kernel arithmetic's default clause (fixture 00753); the int member
    // overlaps the (int, int) clause and is answered there.
    let mut types = Types::new();
    let int = types.int();
    let float = types.float();
    let arrows = vec![
        ResolvedSpecDecl {
            params: vec![int, int],
            result: int,
            constraints: HashMap::new(),
        },
        ResolvedSpecDecl {
            params: vec![float, int],
            result: float,
            constraints: HashMap::new(),
        },
    ];
    let contract = FunctionContract::from_resolved(&mut types, arrows);

    let bad = types.atom_lit("bad");
    let bad_or_int = types.union(bad, int);
    let applied = contract.apply(&mut types, &[bad_or_int, int]);
    assert!(
        applied.enforceable_satisfied,
        "the int member overlaps the (int, int) clause, so the call is not proven to fail"
    );
    let result = applied.result.expect("the overlap answers the clause's result");
    assert!(types.is_equivalent(&result, &int), "got {}", types.display(&result));
}

// ---------------------------------------------------------------------------
// PINNED VERDICTS at the CONTRACT level. Whether a clause fits a call is
// decided by `ContractArrow::narrowed_row` and
// `FunctionContract::admits_instantiated_clause`; whether the CALL is legal is
// decided by `FunctionContract::apply` over the clause SET. These record what
// apply() does with a witness that is the argument.
// ---------------------------------------------------------------------------

fn clause(
    params: Vec<crate::compiler2::types::Ty>,
    result: crate::compiler2::types::Ty,
) -> ResolvedSpecDecl<crate::compiler2::types::Ty> {
    ResolvedSpecDecl {
        params,
        result,
        constraints: HashMap::new(),
    }
}

/// C1. A two-clause POLYMORPHIC contract whose clause domains carry a
/// variable, applied to `{int | binary, int}`. `f({int, a}) :: a` and
/// `f({binary, a}) :: a` each overlap the argument: the first narrows it to
/// `{int, int}` with `a := int`, the second to `{binary, int}` with
/// `a := int`. The call is satisfied and answers `int`. The matched rows are
/// the narrowed rows; `instantiate_open_inputs` instantiates only a column that
/// still carries type variables, so a ground argument like this one is never
/// rewritten and the rows cannot reach a callee's key.
#[test]
fn kdt192_c1_polymorphic_clause_set_overlap() {
    let mut types = Types::new();
    let a = types.type_var(TypeVarId(0));
    let int = types.int();
    let str_t = types.str_t();
    let int_row = types.tuple(&[int, a]);
    let str_row = types.tuple(&[str_t, a]);
    let c1 = clause(vec![int_row], a);
    let c2 = clause(vec![str_row], a);
    let contract = FunctionContract::from_resolved(&mut types, vec![c1, c2]);

    let mixed = types.union(int, str_t);
    let arg = types.tuple(&[mixed, int]);
    let applied = contract.apply(&mut types, &[arg]);
    let rows: Vec<String> = applied
        .matched_arrows
        .iter()
        .map(|row| row.iter().map(|ty| types.display(ty)).collect::<Vec<_>>().join(", "))
        .collect();
    assert_eq!(
        format!(
            "enforceable={} satisfied={} enforceable_satisfied={} rows=[{}] result={}",
            applied.enforceable,
            applied.satisfied,
            applied.enforceable_satisfied,
            rows.join(" | "),
            applied.result.map(|r| types.display(&r)).unwrap_or("-".to_string())
        ),
        "enforceable=true satisfied=true enforceable_satisfied=true rows=[{int, int} | {binary, int}] result=int",
        "C1 polymorphic clause-set overlap"
    );
}

/// C1's binary-field twin: `{int | binary, binary}` at `f({int, a}) :: a` and
/// `f({binary, a}) :: a`. Each clause narrows the first field to its own
/// member and binds `a := binary`, so the call is satisfied and answers
/// `binary`.
#[test]
fn a_polymorphic_clause_set_binds_the_second_field_on_each_clauses_overlap() {
    let mut types = Types::new();
    let a = types.type_var(TypeVarId(0));
    let int = types.int();
    let str_t = types.str_t();
    let int_row = types.tuple(&[int, a]);
    let str_row = types.tuple(&[str_t, a]);
    let c1 = clause(vec![int_row], a);
    let c2 = clause(vec![str_row], a);
    let contract = FunctionContract::from_resolved(&mut types, vec![c1, c2]);

    let mixed = types.union(int, str_t);
    let arg = types.tuple(&[mixed, str_t]);
    let applied = contract.apply(&mut types, &[arg]);

    assert!(applied.enforceable_satisfied);
    assert_eq!(applied.matched_arrows.len(), 2);
    let result = applied.result.expect("both clauses answer");
    assert!(types.is_equivalent(&result, &str_t), "got {}", types.display(&result));
}

/// C2. C1's control: the SAME shape with GROUND clause domains. Each clause
/// narrows the row to its own overlap and answers there.
#[test]
fn kdt192_c2_ground_clause_set_overlap() {
    let mut types = Types::new();
    let int = types.int();
    let str_t = types.str_t();
    let int_row = types.tuple(&[int, int]);
    let str_row = types.tuple(&[str_t, int]);
    let c1 = clause(vec![int_row], int);
    let c2 = clause(vec![str_row], int);
    let contract = FunctionContract::from_resolved(&mut types, vec![c1, c2]);

    let mixed = types.union(int, str_t);
    let arg = types.tuple(&[mixed, int]);
    let applied = contract.apply(&mut types, &[arg]);
    assert_eq!(
        format!(
            "satisfied={} enforceable_satisfied={} rows={}",
            applied.satisfied,
            applied.enforceable_satisfied,
            applied.matched_arrows.len()
        ),
        "satisfied=true enforceable_satisfied=true rows=2",
        "C2 ground clause-set overlap"
    );
}

/// C3. An UNINHABITED argument at a polymorphic contract. `none` is a row no
/// runtime call can supply -- dead code -- so `apply` never refuses it and no
/// violation is diagnosed for code that cannot run. Its ground twin C4
/// answers the same.
#[test]
fn kdt192_c3_none_argument_polymorphic_contract() {
    let mut types = Types::new();
    let a = types.type_var(TypeVarId(0));
    let list_a = types.list(a);
    let c1 = clause(vec![list_a], a);
    let contract = FunctionContract::from_resolved(&mut types, vec![c1]);

    let none = types.none();
    let applied = contract.apply(&mut types, &[none]);
    assert_eq!(
        format!(
            "satisfied={} enforceable_satisfied={}",
            applied.satisfied, applied.enforceable_satisfied
        ),
        "satisfied=true enforceable_satisfied=true",
        "C3 none argument, polymorphic contract"
    );
}

/// C4. The same uninhabited argument at a GROUND contract: C3's control. The
/// two must agree, and do.
#[test]
fn kdt192_c4_none_argument_ground_contract() {
    let mut types = Types::new();
    let int = types.int();
    let list_int = types.list(int);
    let c1 = clause(vec![list_int], int);
    let contract = FunctionContract::from_resolved(&mut types, vec![c1]);

    let none = types.none();
    let applied = contract.apply(&mut types, &[none]);
    assert_eq!(
        format!(
            "satisfied={} enforceable_satisfied={}",
            applied.satisfied, applied.enforceable_satisfied
        ),
        "satisfied=true enforceable_satisfied=true",
        "C4 none argument, ground contract"
    );
}

// ---------------------------------------------------------------------------
// fz-xxd.1: a variadic extern's contract carries its tail. These drive a real
// extern declaration through the ordinary front end (indexing, scoping,
// contract derivation) exactly as a fixture would, then apply the published
// contract directly to a hand-built row, the way `FunctionContract::apply`'s
// caller does.
// ---------------------------------------------------------------------------

/// Drives `source` to a settled program and hands back the named function's
/// published contract, the way a real call site would find it.
fn drive_extern_contract(
    source: &str,
    extern_name: &str,
    fixed_arity: usize,
) -> (Compiler2<ConfiguredTelemetry>, FunctionContract) {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.submit_code(CodeSubmission {
        name: Some(format!("{extern_name}.fz")),
        text: source.to_string(),
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Resolved),
        "a variadic extern and its caller should resolve like any other program"
    );
    let function = compiler
        .world_mut()
        .reference_function(ModuleId::GLOBAL, extern_name, fixed_arity);
    let contract = compiler
        .world()
        .function_contract(function)
        .unwrap_or_else(|| panic!("{extern_name} should publish a function contract"))
        .clone();
    (compiler, contract)
}

#[test]
fn variadic_open_contract_accepts_a_row_widened_from_its_tail_domain() {
    let (mut compiler, contract) = drive_extern_contract(
        "extern \"C\" defp libc::open(path :: c_string, flags :: c_int, ...) :: c_int\n\
         def main() do\n  libc::open(\"/x\", 0, 0o644 :: integer)\nend\n",
        "libc::open",
        2,
    );
    let types = compiler.world_mut().types_mut();
    let binary = types.str_t();
    let int = types.int();

    let applied = contract.apply(types, &[binary, int, int]);
    assert!(
        applied.enforceable_satisfied,
        "open(path, flags, mode) is exactly the declared prefix plus one tail argument"
    );
    let result = applied.result.expect("a fully known row should publish a result");
    assert!(
        types.is_equivalent(&result, &int),
        "open's declared return is integer: {}",
        types.display(&result)
    );
}

#[test]
fn variadic_open_contract_rejects_a_row_shorter_than_its_fixed_prefix() {
    let (mut compiler, contract) = drive_extern_contract(
        "extern \"C\" defp libc::open(path :: c_string, flags :: c_int, ...) :: c_int\n\
         def main() do\n  libc::open(\"/x\", 0, 0o644 :: integer)\nend\n",
        "libc::open",
        2,
    );
    let types = compiler.world_mut().types_mut();
    let binary = types.str_t();

    let applied = contract.apply(types, &[binary]);
    assert!(
        !applied.enforceable_satisfied,
        "a row shorter than open's declared (path, flags) prefix is still Invalid"
    );
    assert!(applied.result.is_none());
}

#[test]
fn variadic_printf_contract_accepts_any_number_of_integer_tail_arguments() {
    let (mut compiler, contract) = drive_extern_contract(
        "extern \"C\" defp libc::printf(fmt :: c_string, ...) :: c_int\n\
         def main() do\n  libc::printf(\"%lld %lld %lld\\n\", 11, 22, 33)\nend\n",
        "libc::printf",
        1,
    );
    let types = compiler.world_mut().types_mut();
    let binary = types.str_t();
    let int = types.int();

    let three_tail_args = contract.apply(types, &[binary, int, int, int]);
    assert!(
        three_tail_args.enforceable_satisfied,
        "printf(fmt, 11, 22, 33) widens the tail to three integers"
    );
    let one_tail_arg = contract.apply(types, &[binary, int]);
    assert!(
        one_tail_arg.enforceable_satisfied,
        "printf(fmt, 9) widens the tail to one integer"
    );
}

#[test]
fn variadic_printf_contract_rejects_a_float_tail_argument() {
    let (mut compiler, contract) = drive_extern_contract(
        "extern \"C\" defp libc::printf(fmt :: c_string, ...) :: c_int\n\
         def main() do\n  libc::printf(\"%d\", 7)\nend\n",
        "libc::printf",
        1,
    );
    let types = compiler.world_mut().types_mut();
    let binary = types.str_t();
    let float = types.float();

    let applied = contract.apply(types, &[binary, float]);
    assert!(
        !applied.enforceable_satisfied,
        "a float tail argument is outside the declaration's tail domain: printf(fmt, 1.5) has no answer"
    );
    assert!(applied.result.is_none());
}

#[test]
fn variadic_printf_contract_accepts_a_binary_tail_argument() {
    let (mut compiler, contract) = drive_extern_contract(
        "extern \"C\" defp libc::printf(fmt :: c_string, ...) :: c_int\n\
         def main() do\n  libc::printf(\"%d\", 7)\nend\n",
        "libc::printf",
        1,
    );
    let types = compiler.world_mut().types_mut();
    let binary = types.str_t();

    let applied = contract.apply(types, &[binary, binary]);
    assert!(
        applied.enforceable_satisfied,
        "an ascribed binary tail argument reaches the wire, so the contract must accept it: printf(fmt, s :: cstring)"
    );
}

// ---------------------------------------------------------------------------
// A call is refused only when its argument row fits no clause of the
// contract. A row that overlaps a clause is answered on the overlap: each
// ground column is narrowed to the clause's domain, and the clause's result
// stands for the part that can return. `any` is just the widest overlap: the
// call site does not know the argument's type, the way Elixir reads a
// `dynamic()` argument.
//
// Two places have no run-time clause test that could catch a miss, so an
// overlap that is not a fit is still refused there: an extern's raw machine
// call, and a brand, which the running program cannot see.
// ---------------------------------------------------------------------------

/// Drives a program that reaches `Kernel`'s private `fz_resource_claim`
/// extern and hands back its published contract, the way a real call site
/// would find it. `"fz"`-ABI externs are reserved to bootstrap source
/// (`declared_by_runtime_library`), so this drives the REAL declaration in
/// `lib/kernel.fz` — which is loaded for every program — instead of
/// restating one in test source.
fn drive_kernel_resource_claim_contract() -> (Compiler2<ConfiguredTelemetry>, FunctionContract) {
    let tel = ConfiguredTelemetry::new();
    let mut compiler = Compiler2::new(tel);
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.submit_code(CodeSubmission {
        name: Some("drives_kernel_resource_claim.fz".to_string()),
        text: "def main() do\n  Kernel.claim_resource(Kernel.make_resource(42, fn (_x) -> nil end))\nend\n".to_string(),
    });
    let outcome = compiler.drive();
    assert!(
        matches!(outcome, DriveOutcome::Resolved),
        "a program that reaches Kernel.claim_resource should resolve like any other: {outcome:?}"
    );
    let kernel = compiler
        .world_mut()
        .reference_module(ModuleName::parse_dotted("Kernel").expect("Kernel module name"));
    let function = compiler.world_mut().reference_function(kernel, "fz_resource_claim", 1);
    let contract = compiler
        .world()
        .function_contract(function)
        .expect("fz_resource_claim should publish a function contract")
        .clone();
    (compiler, contract)
}

#[test]
fn fz_resource_claim_contract_applied_to_an_any_argument_answers_boolean() {
    let (mut compiler, contract) = drive_kernel_resource_claim_contract();
    let types = compiler.world_mut().types_mut();
    let any = types.any();

    let applied = contract.apply(types, &[any]);
    assert!(
        applied.satisfied,
        "a handle whose type is unknown (any) is narrowed to the resource domain, not rejected as a mismatch"
    );
    let boolean = types.bool();
    let result = applied
        .result
        .expect("a handle narrowed into the resource domain still publishes a result");
    assert!(
        types.is_equivalent(&result, &boolean),
        "fz_resource_claim's declared return is boolean: {}",
        types.display(&result)
    );
}

#[test]
fn fz_resource_claim_contract_rejects_an_atom_argument() {
    let (mut compiler, contract) = drive_kernel_resource_claim_contract();
    let types = compiler.world_mut().types_mut();
    let atom = types.atom_lit("atom");

    let applied = contract.apply(types, &[atom]);
    assert!(
        !applied.satisfied,
        "an atom is a precisely known value outside the resource domain, not an imprecise one to narrow"
    );
    assert!(applied.result.is_none());
}

fn integer_contract(types: &mut Types) -> FunctionContract {
    let int = types.int();
    let resolved = ResolvedSpecDecl {
        params: vec![int],
        result: int,
        constraints: HashMap::new(),
    };
    FunctionContract::from_resolved(types, vec![resolved])
}

fn one_integer_wire() -> crate::compiler2::body::LoweredExtern {
    crate::compiler2::body::LoweredExtern {
        abi: crate::fz_ir::ExternAbi::C,
        symbol: "takes_an_integer".to_string(),
        params: vec![crate::fz_ir::ExternTy::I64],
        variadic: false,
        ret: crate::fz_ir::ExternReturn::scalar(crate::fz_ir::ExternTy::I64),
    }
}

#[test]
fn a_union_overlapping_an_integer_function_domain_is_answered_on_the_overlap() {
    let mut types = Types::new();
    let int = types.int();
    let contract = integer_contract(&mut types);

    let weird = types.atom_lit("weird");
    let int_or_weird = types.union(int, weird);
    let applied = contract.apply(&mut types, &[int_or_weird]);

    assert!(
        applied.enforceable_satisfied,
        "integer | :weird overlaps the integer domain: a function tests its clauses at run time, so only the integer reaches the body"
    );
    let result = applied.result.expect("the overlap answers the clause's result");
    assert!(types.is_equivalent(&result, &int), "got {}", types.display(&result));
}

#[test]
fn an_extern_refuses_a_union_that_spills_outside_its_domain() {
    let mut types = Types::new();
    let int = types.int();
    let contract = integer_contract(&mut types).with_extern_wire(one_integer_wire());

    let weird = types.atom_lit("weird");
    let int_or_weird = types.union(int, weird);
    let applied = contract.apply(&mut types, &[int_or_weird]);

    assert!(
        !applied.satisfied,
        "an extern is a raw machine call with no clause tests, so a value outside its domain would reach the wire"
    );
    assert!(applied.result.is_none());
}

fn make_resource_contract(types: &mut Types) -> FunctionContract {
    let t = TypeVarId(0);
    let var = types.type_var(t);
    let nil = types.nil();
    let destructor = types.arrow(&[var], nil);
    let int = types.int();
    let pointer = types.c_pointer();
    let bound = types.union(int, pointer);
    let result = types.resource(var);
    let resolved = ResolvedSpecDecl {
        params: vec![var, destructor],
        result,
        constraints: HashMap::from([(t, bound)]),
    };
    let wire = crate::compiler2::body::LoweredExtern {
        abi: crate::fz_ir::ExternAbi::C,
        symbol: "make_resource".to_string(),
        params: vec![crate::fz_ir::ExternTy::I64, crate::fz_ir::ExternTy::Any],
        variadic: false,
        ret: crate::fz_ir::ExternReturn::scalar(crate::fz_ir::ExternTy::Any),
    };
    FunctionContract::from_resolved(types, vec![resolved]).with_extern_wire(wire)
}

#[test]
fn an_extern_accepts_a_callable_whose_parameter_is_the_instantiated_variable() {
    let mut types = Types::new();
    let int = types.int();
    let nil = types.nil();
    let contract = make_resource_contract(&mut types);

    let destructor = types.arrow(&[int], nil);
    let applied = contract.apply(&mut types, &[int, destructor]);

    assert!(
        applied.satisfied,
        "(int) -> nil is the destructor the domain admits at t := int"
    );
    let result = applied.result.expect("a satisfied extern answers its result");
    let expected = types.resource(int);
    assert!(
        types.is_equivalent(&result, &expected),
        "got {}",
        types.display(&result)
    );
}

#[test]
fn an_extern_refuses_a_payload_outside_its_variable_bound() {
    let mut types = Types::new();
    let int = types.int();
    let nil = types.nil();
    let bin = types.str_t();
    let contract = make_resource_contract(&mut types);

    let destructor = types.arrow(&[int], nil);
    let applied = contract.apply(&mut types, &[bin, destructor]);

    assert!(!applied.satisfied, "a binary payload is outside t: integer | c_pointer");
}

#[test]
fn an_extern_refuses_a_callable_whose_return_is_outside_the_instantiated_destructor() {
    let mut types = Types::new();
    let int = types.int();
    let bin = types.str_t();
    let contract = make_resource_contract(&mut types);

    let wrong_destructor = types.arrow(&[int], bin);
    let applied = contract.apply(&mut types, &[int, wrong_destructor]);

    assert!(
        !applied.satisfied,
        "at t := int the destructor is (int) -> nil; (int) -> binary is not that"
    );
}

#[test]
fn an_extern_narrows_an_any_argument_to_its_domain() {
    let mut types = Types::new();
    let int = types.int();
    let any = types.any();
    let contract = integer_contract(&mut types).with_extern_wire(one_integer_wire());

    let applied = contract.apply(&mut types, &[any]);

    assert!(
        applied.satisfied,
        "any is an unknown type, not a claim to be every value"
    );
    let result = applied.result.expect("an any argument answers the clause's result");
    assert!(types.is_equivalent(&result, &int));
}

#[test]
fn an_any_column_narrows_and_a_disjoint_sibling_column_still_rejects() {
    let mut types = Types::new();
    let int = types.int();
    let resolved = ResolvedSpecDecl {
        params: vec![int, int],
        result: int,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let any = types.any();
    let weird = types.atom_lit("weird");
    let applied = contract.apply(&mut types, &[any, weird]);

    assert!(
        !applied.satisfied,
        "the any column alone would narrow to integer, but :weird in the sibling column fits no clause"
    );
    assert!(applied.result.is_none());
}

#[test]
fn a_bare_inner_is_refused_at_a_brand_domain_even_when_a_sibling_member_fits() {
    let mut types = Types::new();
    let bin = types.str_t();
    let int = types.int();
    let utf8 = types.mint_brand(bin, "utf8");
    let resolved = ResolvedSpecDecl {
        params: vec![utf8],
        result: int,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let bin_or_int = types.union(bin, int);
    let applied = contract.apply(&mut types, &[bin_or_int]);

    assert!(
        !applied.satisfied,
        "the runtime cannot tell a binary from a utf8, so the binary member would pass the clause test unchecked"
    );
}

#[test]
fn a_bare_inner_is_refused_at_a_brand_inside_a_tuple_domain() {
    let mut types = Types::new();
    let bin = types.str_t();
    let int = types.int();
    let utf8 = types.mint_brand(bin, "utf8");
    let branded_pair = types.tuple(&[utf8, int]);
    let resolved = ResolvedSpecDecl {
        params: vec![branded_pair],
        result: int,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let bare_pair = types.tuple(&[bin, int]);
    let applied = contract.apply(&mut types, &[bare_pair]);

    assert!(
        !applied.satisfied,
        "a brand in a tuple field is as invisible to the clause test as one at the top"
    );
}

#[test]
fn a_brand_is_accepted_at_its_own_brand_domain() {
    let mut types = Types::new();
    let bin = types.str_t();
    let int = types.int();
    let utf8 = types.mint_brand(bin, "utf8");
    let resolved = ResolvedSpecDecl {
        params: vec![utf8],
        result: int,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let applied = contract.apply(&mut types, &[utf8]);

    assert!(
        applied.enforceable_satisfied,
        "a utf8 fits a utf8 domain: the part of it the runtime lets in lies inside the domain"
    );
}

#[test]
fn a_union_spanning_two_clauses_is_answered_by_each_clause_on_its_overlap() {
    let mut types = Types::new();
    let int = types.int();
    let float = types.float();
    let arrows = vec![
        ResolvedSpecDecl {
            params: vec![int, int],
            result: int,
            constraints: HashMap::new(),
        },
        ResolvedSpecDecl {
            params: vec![float, int],
            result: float,
            constraints: HashMap::new(),
        },
    ];
    let contract = FunctionContract::from_resolved(&mut types, arrows);

    let int_or_float = types.union(int, float);
    let applied = contract.apply(&mut types, &[int_or_float, int]);

    assert!(applied.enforceable_satisfied);
    assert_eq!(applied.matched_arrows.len(), 2, "each clause matched its own slice");
    let result = applied.result.expect("both clauses answer");
    assert!(
        types.is_equivalent(&result, &int_or_float),
        "int from the integer clause joined with float from the float clause, got {}",
        types.display(&result)
    );
}

// fz-xxd.6: an extern's declaration is its whole contract. `libc::abs` takes
// one `c_int`, and `:nope` fits no clause of that contract, so the call is
// rejected at compile time on every door -- there is no extern body to fall
// back into, and no backend may be asked to make the call.
#[test]
fn extern_row_outside_its_declared_contract_is_a_spec_violation() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/00605_libc_abs_arg_outside_declared_domain.fz".to_string()),
        text: include_str!("../../fixtures/00605_libc_abs_arg_outside_declared_domain.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "an extern row outside its declared contract should fail to compile",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("the rejected extern row must surface as a diagnostic");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::SPEC_VIOLATION.0);
    let message = metadata_str(&diagnostic, "message");
    assert!(
        message.contains("libc::abs"),
        "the diagnostic should name the extern, got: {message}",
    );
    assert!(
        message.contains(":nope"),
        "the diagnostic should name the rejected row, got: {message}",
    );
    assert!(
        message.contains("declared domain is (int)"),
        "the diagnostic should name the declared domain, got: {message}",
    );
}

// fz-xxd.6: a variadic extern's contract accepts more past its fixed
// parameters, so a violation naming only the fixed parameters understates
// what the call was actually checked against. `libc::printf` declares one
// fixed parameter (`fmt`); the domain named here must also name what its
// tail accepts.
#[test]
fn variadic_extern_violation_names_the_tail_domain_past_the_fixed_params() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    capture.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("fixtures/00253_variadic_float_error.fz".to_string()),
        text: include_str!("../../fixtures/00253_variadic_float_error.fz").to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        matches!(compiler.drive(), DriveOutcome::Fatal { .. }),
        "a float tail argument is outside the declaration's tail domain",
    );
    let diagnostic = capture
        .last(&["fz", "diag", "error"])
        .expect("the rejected extern row must surface as a diagnostic");
    assert_eq!(metadata_str(&diagnostic, "code"), codes::SPEC_VIOLATION.0);
    let message = metadata_str(&diagnostic, "message");
    assert!(
        message.contains("declared domain is (binary, ..."),
        "the domain should name the fixed `fmt` parameter and then the tail's own domain \
         marked `...`, not stop at the fixed parameters, got: {message}",
    );
}

#[test]
fn a_protocol_domain_parameter_refines_an_untyped_argument_as_any_and_keeps_its_obligation() {
    let mut types = Types::new();
    let domain = types.protocol_domain_of(enumerable_protocol());
    let int = types.int();
    let any = types.any();
    let resolved = ResolvedSpecDecl {
        params: vec![domain],
        result: int,
        constraints: HashMap::new(),
    };
    let contract = FunctionContract::from_resolved(&mut types, vec![resolved]);

    let applied = contract.apply(&mut types, &[any]);

    assert_eq!(
        applied.matched_arrows,
        vec![vec![any]],
        "a call refines its inputs by the structural surface, where the marker is any value"
    );
    assert_eq!(
        contract.arrows[0].protocol_domain_obligations,
        BTreeSet::from([ProtocolDomainObligation::from_protocol(enumerable_protocol())]),
        "the declared arrow still carries the obligation the surface does not"
    );
}

#[test]
fn a_protocol_domain_nested_in_a_parameter_is_read_as_any_in_the_surface() {
    let mut types = Types::new();
    let domain = types.protocol_domain_of(enumerable_protocol());
    let int = types.int();
    let any = types.any();
    let list_of_any = types.list(any);
    let list_of_domain = types.list(domain);

    assert_eq!(
        types.structural_surface(list_of_domain),
        list_of_any,
        "a marker inside a list element is any value"
    );
    assert_eq!(
        types.structural_surface(int),
        int,
        "a type with no marker is its own surface"
    );
}
