use super::{
    CallbackReturnDemand, CallbackReturnFact, ResolvedSpec, ResolvedSpecSet, ResolvedTypeShape,
    SchemeInstantiation, SpecApplicationOutcome, apply_spec_set,
    declared_specs_cover_inferred_spec, instantiate_match, matching_result, resolve_closure_return,
    unique_matching_params,
};
use crate::types::{ClosureTarget, ClosureTypes, ConcreteTypes, MapKey, TypeVarId, Types};

fn resolved_spec(params: Vec<crate::types::Ty>, result: crate::types::Ty) -> ResolvedSpec {
    let param_shapes = vec![ResolvedTypeShape::Any; params.len()];
    ResolvedSpec {
        params,
        param_shapes,
        result,
        result_shape: ResolvedTypeShape::Any,
        constraints: std::collections::HashMap::new(),
    }
}

#[test]
fn scheme_result_instantiates_tuple_from_param_witnesses() {
    let mut t = ConcreteTypes;
    let a = t.type_var(crate::types::TypeVarId(0));
    let b = t.type_var(crate::types::TypeVarId(1));
    let result = t.tuple(&[a.clone(), b.clone()]);
    let one = t.int_lit(1);
    let ok = t.atom_lit("ok");

    let constraints = std::collections::HashMap::new();
    let instantiated = instantiate_match(&mut t, &[a, b], &result, &constraints, &[one, ok]);

    let SchemeInstantiation::Known(matched) = instantiated else {
        panic!("expected concrete tuple instantiation, got {instantiated:?}");
    };
    let tuple = matched.result;
    let Some(elems) = t.tuple_lit_elems(&tuple) else {
        panic!("expected tuple result, got {}", t.display(&tuple));
    };
    assert_eq!(t.as_int_singleton(&elems[0]), Some(1));
    assert_eq!(t.as_atom_singleton(&elems[1]).as_deref(), Some("ok"));
}

#[test]
fn scheme_result_instantiates_list_element_witness() {
    let mut t = ConcreteTypes;
    let a = t.type_var(crate::types::TypeVarId(0));
    let param = t.list(a.clone());
    let result = a;
    let witness_elem = t.int_lit(7);
    let witness = t.list(witness_elem);

    let constraints = std::collections::HashMap::new();
    let instantiated = instantiate_match(&mut t, &[param], &result, &constraints, &[witness]);

    let SchemeInstantiation::Known(matched) = instantiated else {
        panic!("expected list element instantiation, got {instantiated:?}");
    };
    let elem = matched.result;
    assert_eq!(t.as_int_singleton(&elem), Some(7));
}

#[test]
fn scheme_result_instantiates_resource_payload_witness() {
    let mut t = ConcreteTypes;
    let a = t.type_var(crate::types::TypeVarId(0));
    let param = t.resource(a.clone());
    let result = a;
    let witness_payload = t.atom_lit("socket");
    let witness = t.resource(witness_payload);

    let constraints = std::collections::HashMap::new();
    let instantiated = instantiate_match(&mut t, &[param], &result, &constraints, &[witness]);

    let SchemeInstantiation::Known(matched) = instantiated else {
        panic!("expected resource payload instantiation, got {instantiated:?}");
    };
    let payload = matched.result;
    assert_eq!(t.as_atom_singleton(&payload).as_deref(), Some("socket"));
}

#[test]
fn scheme_result_reports_underconstrained_free_result_var() {
    let mut t = ConcreteTypes;
    let param = t.int();
    let result = t.type_var(crate::types::TypeVarId(9));
    let witness = t.int_lit(1);

    let constraints = std::collections::HashMap::new();
    let instantiated = instantiate_match(&mut t, &[param], &result, &constraints, &[witness]);

    assert!(
        matches!(instantiated, SchemeInstantiation::Underconstrained(_)),
        "free result var must not be reported as known: {instantiated:?}"
    );
}

#[test]
fn scheme_result_widens_reduce_while_accumulator_from_reducer_exits() {
    let mut t = ConcreteTypes;
    let entry_var = t.type_var(crate::types::TypeVarId(0));
    let acc_var = t.type_var(crate::types::TypeVarId(1));
    let reducer_result = {
        let cont = t.atom_lit("cont");
        let halt = t.atom_lit("halt");
        let cont_tuple = t.tuple(&[cont, acc_var.clone()]);
        let halt_tuple = t.tuple(&[halt, acc_var.clone()]);
        t.union(cont_tuple, halt_tuple)
    };
    let reducer_pattern = t.arrow(&[entry_var, acc_var.clone()], reducer_result);

    let not_found = t.atom_lit("not_found");
    let found = t.atom_lit("found");
    let zero = t.int_lit(0);
    let initial_acc = t.tuple(&[not_found.clone(), zero]);
    let any_int = t.int();
    let not_found_int = t.tuple(&[not_found, any_int.clone()]);
    let found_int = t.tuple(&[found, any_int]);
    let reducer_witness_result = {
        let cont = t.atom_lit("cont");
        let halt = t.atom_lit("halt");
        let cont_tuple = t.tuple(&[cont, not_found_int.clone()]);
        let halt_tuple = t.tuple(&[halt, found_int.clone()]);
        t.union(cont_tuple, halt_tuple)
    };
    let reducer_entry_arg = t.any();
    let reducer_acc_arg = t.any();
    let reducer_witness = t.arrow(
        &[reducer_entry_arg, reducer_acc_arg],
        reducer_witness_result,
    );

    let constraints = std::collections::HashMap::new();
    let instantiated = instantiate_match(
        &mut t,
        &[acc_var.clone(), reducer_pattern],
        &acc_var,
        &constraints,
        &[initial_acc, reducer_witness],
    );

    let SchemeInstantiation::Known(matched) = instantiated else {
        panic!("expected known accumulator union, got {instantiated:?}");
    };
    let acc = matched.result;
    let expected = t.union(not_found_int, found_int);
    assert!(
        t.is_equivalent(&acc, &expected),
        "expected widened accumulator {}, got {}",
        t.display(&expected),
        t.display(&acc)
    );
}

#[test]
fn scheme_result_rejects_structural_witness_mismatch() {
    let mut t = ConcreteTypes;
    let a = t.type_var(crate::types::TypeVarId(0));
    let param = t.tuple(&[a.clone()]);
    let witness = t.int_lit(1);

    let constraints = std::collections::HashMap::new();
    let instantiated = instantiate_match(&mut t, &[param], &a, &constraints, &[witness]);

    assert!(
        matches!(instantiated, SchemeInstantiation::Invalid),
        "mismatched tuple witness must not produce a fact: {instantiated:?}"
    );
}

#[test]
fn scheme_result_instantiates_map_field_witness() {
    let mut t = ConcreteTypes;
    let a = t.type_var(crate::types::TypeVarId(0));
    let key = MapKey::Atom("value".to_string());
    let param = t.map(&[(key.clone(), a.clone())]);
    let result = t.tuple(&[a]);
    let witness_field = t.int_lit(42);
    let witness = t.map(&[(key, witness_field)]);

    let constraints = std::collections::HashMap::new();
    let instantiated = instantiate_match(&mut t, &[param], &result, &constraints, &[witness]);

    let SchemeInstantiation::Known(matched) = instantiated else {
        panic!("expected map field instantiation, got {instantiated:?}");
    };
    let tuple = matched.result;
    let Some(elems) = t.tuple_lit_elems(&tuple) else {
        panic!("expected tuple result, got {}", t.display(&tuple));
    };
    assert_eq!(t.as_int_singleton(&elems[0]), Some(42));
}

#[test]
fn callable_scheme_result_instantiates_tuple_from_call_args() {
    let mut t = ConcreteTypes;
    let a = t.type_var(crate::types::TypeVarId(0));
    let b = t.type_var(crate::types::TypeVarId(1));
    let ret = t.tuple(&[a.clone(), b.clone()]);
    let closure = t.arrow(&[a, b], ret);
    let one = t.int_lit(1);
    let ok = t.atom_lit("ok");

    let result = resolve_closure_return(
        &mut t,
        &closure,
        &std::collections::HashMap::new(),
        &[one, ok],
    )
    .expect("plain callable clause should resolve immediately");

    let Some(elems) = t.tuple_lit_elems(&result) else {
        panic!("expected tuple return, got {}", t.display(&result));
    };
    assert_eq!(t.as_int_singleton(&elems[0]), Some(1));
    assert_eq!(t.as_atom_singleton(&elems[1]).as_deref(), Some("ok"));
}

#[test]
fn resolved_spec_set_selects_return_by_matching_arrow() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let float = ct.float();
    let set = ResolvedSpecSet {
        arrows: vec![
            ResolvedSpec {
                params: vec![int.clone()],
                param_shapes: vec![ResolvedTypeShape::Any],
                result: int.clone(),
                result_shape: ResolvedTypeShape::Any,
                constraints: std::collections::HashMap::new(),
            },
            ResolvedSpec {
                params: vec![float.clone()],
                param_shapes: vec![ResolvedTypeShape::Any],
                result: float.clone(),
                result_shape: ResolvedTypeShape::Any,
                constraints: std::collections::HashMap::new(),
            },
        ],
    };

    let int_arg = ct.int_lit(1);
    let int_result = matching_result(&mut ct, &set, &[int_arg]).unwrap();
    assert!(ct.is_equivalent(&int_result, &int));

    let float_arg = ct.float_lit(1.5);
    let float_result = matching_result(&mut ct, &set, &[float_arg]).unwrap();
    assert!(ct.is_equivalent(&float_result, &float));
}

#[test]
fn resolved_spec_set_unions_results_only_after_arrow_selection() {
    let mut ct = ConcreteTypes;
    let int = ct.int();
    let float = ct.float();
    let set = ResolvedSpecSet {
        arrows: vec![
            ResolvedSpec {
                params: vec![int.clone()],
                param_shapes: vec![ResolvedTypeShape::Any],
                result: int.clone(),
                result_shape: ResolvedTypeShape::Any,
                constraints: std::collections::HashMap::new(),
            },
            ResolvedSpec {
                params: vec![float.clone()],
                param_shapes: vec![ResolvedTypeShape::Any],
                result: float.clone(),
                result_shape: ResolvedTypeShape::Any,
                constraints: std::collections::HashMap::new(),
            },
            ResolvedSpec {
                params: vec![int.clone()],
                param_shapes: vec![ResolvedTypeShape::Any],
                result: float.clone(),
                result_shape: ResolvedTypeShape::Any,
                constraints: std::collections::HashMap::new(),
            },
        ],
    };

    let int_arg = ct.int_lit(1);
    let int_result = matching_result(&mut ct, &set, &[int_arg.clone()]).unwrap();
    assert!(ct.is_subtype(&int, &int_result));
    assert!(ct.is_subtype(&float, &int_result));

    let params = unique_matching_params(&mut ct, &set, &[int_arg]);
    assert!(
        params.is_none(),
        "input demand should stay with the concrete call when several arrows match"
    );
}

#[test]
fn declared_spec_coverage_accepts_matching_overload_arrow() {
    let mut t = ConcreteTypes;
    let int = t.int();
    let float = t.float();
    let set = ResolvedSpecSet {
        arrows: vec![
            resolved_spec(vec![int.clone()], int.clone()),
            resolved_spec(vec![float.clone()], float.clone()),
        ],
    };

    let inferred_inputs = vec![Some(t.float_lit(1.5))];
    let inferred_result = t.float_lit(2.5);

    assert!(declared_specs_cover_inferred_spec(
        &mut t,
        &set,
        &inferred_inputs,
        &inferred_result,
    ));
}

#[test]
fn declared_spec_coverage_preserves_overload_param_result_correlation() {
    let mut t = ConcreteTypes;
    let int = t.int();
    let float = t.float();
    let set = ResolvedSpecSet {
        arrows: vec![
            resolved_spec(vec![int.clone()], int),
            resolved_spec(vec![float.clone()], float),
        ],
    };

    let inferred_inputs = vec![Some(t.int_lit(1))];
    let inferred_result = t.float_lit(2.5);

    assert!(
        !declared_specs_cover_inferred_spec(&mut t, &set, &inferred_inputs, &inferred_result),
        "an int input must not borrow the float overload's result"
    );
}

#[test]
fn declared_spec_coverage_allows_hole_when_result_is_still_proven() {
    let mut t = ConcreteTypes;
    let int = t.int();
    let set = ResolvedSpecSet {
        arrows: vec![resolved_spec(vec![int.clone(), int.clone()], int)],
    };

    let inferred_inputs = vec![None, Some(t.int_lit(1))];
    let inferred_result = t.int_lit(2);

    assert!(declared_specs_cover_inferred_spec(
        &mut t,
        &set,
        &inferred_inputs,
        &inferred_result,
    ));
}

#[test]
fn declared_spec_coverage_rejects_hole_that_leaves_result_underconstrained() {
    let mut t = ConcreteTypes;
    let a = t.type_var(TypeVarId(0));
    let int = t.int();
    let set = ResolvedSpecSet {
        arrows: vec![resolved_spec(vec![a.clone(), int], a)],
    };

    let inferred_inputs = vec![None, Some(t.int_lit(1))];
    let inferred_result = t.int_lit(2);

    assert!(
        !declared_specs_cover_inferred_spec(&mut t, &set, &inferred_inputs, &inferred_result),
        "a positional hole is unknown evidence, not an `any` witness for a result variable"
    );
}

#[test]
fn spec_application_unions_successful_overlap_returns() {
    let mut t = ConcreteTypes;
    let int = t.int();
    let float = t.float();
    let set = ResolvedSpecSet {
        arrows: vec![
            resolved_spec(vec![int.clone(), int.clone()], int.clone()),
            resolved_spec(vec![float.clone(), int.clone()], float.clone()),
        ],
    };

    let any = t.any();
    let outcome = apply_spec_set::<_, (), _>(&mut t, &set, &[any, int], |_t, _query| None);
    let SpecApplicationOutcome::Known(application) = outcome else {
        panic!("expected successful application, got {outcome:?}");
    };
    let expected_int = t.int();
    let expected_float = t.float();
    let expected = t.union(expected_int, expected_float);
    assert!(
        t.is_equivalent(&application.result, &expected),
        "successful overlap returns should union to {}, got {}",
        t.display(&expected),
        t.display(&application.result)
    );
    assert_eq!(application.matched_arrows.len(), 2);
    assert!(application.complete);
}

#[test]
fn spec_application_reports_no_match_for_proved_contradiction() {
    let mut t = ConcreteTypes;
    let int = t.int();
    let set = ResolvedSpecSet {
        arrows: vec![resolved_spec(vec![int.clone()], int)],
    };

    let float = t.float();
    let outcome = apply_spec_set::<_, (), _>(&mut t, &set, &[float], |_t, _query| None);

    assert!(
        matches!(outcome, SpecApplicationOutcome::NoMatch),
        "disjoint input should be a proved no-match, got {outcome:?}"
    );
}

#[test]
fn spec_application_reports_underconstrained_free_result() {
    let mut t = ConcreteTypes;
    let int = t.int();
    let result = t.type_var(TypeVarId(0));
    let set = ResolvedSpecSet {
        arrows: vec![resolved_spec(vec![int.clone()], result)],
    };

    let outcome = apply_spec_set::<_, (), _>(&mut t, &set, &[int], |_t, _query| None);

    let SpecApplicationOutcome::Underconstrained(application) = outcome else {
        panic!("free result variable should remain underconstrained, got {outcome:?}");
    };
    assert!(
        application
            .partial_result
            .as_ref()
            .is_some_and(|result| t.has_vars(result)),
        "underconstrained application should carry the partial result"
    );
}

#[test]
fn spec_application_tracks_pending_callback_return_reads() {
    let mut t = ConcreteTypes;
    let set = reduce_while_spec_set(&mut t);
    let not_found = t.atom_lit("not_found");
    let zero = t.int_lit(0);
    let initial_acc = t.tuple(&[not_found, zero]);
    let entry = t.int();
    let list = t.list(entry);
    let target = ClosureTarget(7);
    let reducer = t.closure_lit(target, Vec::new(), 2);

    let outcome = apply_spec_set(&mut t, &set, &[list, initial_acc, reducer], |_t, query| {
        assert_eq!(query.target, target);
        assert_eq!(query.demand, CallbackReturnDemand::TupleFields(2));
        Some(CallbackReturnFact::Pending { read: "reducer" })
    });

    let SpecApplicationOutcome::Known(application) = outcome else {
        panic!("initial accumulator should still prove a partial result, got {outcome:?}");
    };
    assert!(!application.complete);
    assert_eq!(application.reads, vec!["reducer"]);
}

#[test]
fn spec_application_refines_result_from_callback_return_witness() {
    let mut t = ConcreteTypes;
    let set = reduce_while_spec_set(&mut t);
    let not_found = t.atom_lit("not_found");
    let found = t.atom_lit("found");
    let zero = t.int_lit(0);
    let initial_acc = t.tuple(&[not_found.clone(), zero]);
    let entry = t.int();
    let list = t.list(entry);
    let target = ClosureTarget(9);
    let reducer = t.closure_lit(target, Vec::new(), 2);
    let reducer_return = {
        let int = t.int();
        let not_found_int = t.tuple(&[not_found, int.clone()]);
        let found_int = t.tuple(&[found.clone(), int]);
        let cont_atom = t.atom_lit("cont");
        let halt_atom = t.atom_lit("halt");
        let cont = t.tuple(&[cont_atom, not_found_int]);
        let halt = t.tuple(&[halt_atom, found_int]);
        t.union(cont, halt)
    };

    let outcome = apply_spec_set(&mut t, &set, &[list, initial_acc, reducer], |_t, query| {
        assert_eq!(query.target, target);
        Some(CallbackReturnFact::Known {
            result: reducer_return.clone(),
            read: "reducer",
            complete: true,
        })
    });

    let SpecApplicationOutcome::Known(application) = outcome else {
        panic!("callback return witness should produce a known result, got {outcome:?}");
    };
    let int = t.int();
    let found_int = t.tuple(&[found, int]);
    assert!(
        t.is_subtype(&found_int, &application.result),
        "callback halt payload should flow into reduce result, got {}",
        t.display(&application.result)
    );
    assert!(application.complete);
    assert_eq!(application.reads, vec!["reducer"]);
}

fn reduce_while_spec_set(t: &mut ConcreteTypes) -> ResolvedSpecSet {
    let entry_var = t.type_var(TypeVarId(0));
    let acc_var = t.type_var(TypeVarId(1));
    let reducer_ret = {
        let cont = t.atom_lit("cont");
        let halt = t.atom_lit("halt");
        let cont_tuple = t.tuple(&[cont, acc_var.clone()]);
        let halt_tuple = t.tuple(&[halt, acc_var.clone()]);
        t.union(cont_tuple, halt_tuple)
    };
    let enumerable_param = t.list(entry_var.clone());
    let reducer_param = t.arrow(&[entry_var, acc_var.clone()], reducer_ret);
    ResolvedSpecSet {
        arrows: vec![ResolvedSpec {
            params: vec![enumerable_param, acc_var.clone(), reducer_param],
            param_shapes: vec![
                ResolvedTypeShape::List(Box::new(ResolvedTypeShape::Var(TypeVarId(0)))),
                ResolvedTypeShape::Var(TypeVarId(1)),
                ResolvedTypeShape::Arrow {
                    params: vec![
                        ResolvedTypeShape::Var(TypeVarId(0)),
                        ResolvedTypeShape::Var(TypeVarId(1)),
                    ],
                    result: Box::new(ResolvedTypeShape::Union(vec![
                        ResolvedTypeShape::Tuple(vec![
                            ResolvedTypeShape::AtomLit("cont".to_string()),
                            ResolvedTypeShape::Var(TypeVarId(1)),
                        ]),
                        ResolvedTypeShape::Tuple(vec![
                            ResolvedTypeShape::AtomLit("halt".to_string()),
                            ResolvedTypeShape::Var(TypeVarId(1)),
                        ]),
                    ])),
                },
            ],
            result: acc_var,
            result_shape: ResolvedTypeShape::Var(TypeVarId(1)),
            constraints: std::collections::HashMap::new(),
        }],
    }
}
