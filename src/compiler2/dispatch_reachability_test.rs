use super::*;
use crate::ast::{Expr, Pattern, Spanned};
use crate::compiler2::types::{MapKey, Sigma, TypeVarId};
use crate::dispatch_matrix::demand::DispatchDemand;
use crate::dispatch_matrix::pattern::{PatternRow, PatternSubjectRef, SourcePatternRows, pattern_dispatch_from_source};

fn row(pattern: Pattern, body_id: u32) -> PatternRow<Ty> {
    PatternRow {
        patterns: vec![Spanned::dummy(pattern)],
        preconditions: Vec::new(),
        guard: None,
        body_id,
    }
}

fn row2(first: Pattern, second: Pattern, body_id: u32) -> PatternRow<Ty> {
    PatternRow {
        patterns: vec![Spanned::dummy(first), Spanned::dummy(second)],
        preconditions: Vec::new(),
        guard: None,
        body_id,
    }
}

/// A guard uses a carrier subject to enter the graph, but that carrier is
/// not necessarily a runtime read. Its leaves are the authority for which
/// roots reachability may envelope.
#[test]
fn a_guard_envelopes_only_the_input_its_leaves_read() {
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        3,
        vec![
            PatternRow {
                patterns: vec![
                    Spanned::dummy(Pattern::Var("first".to_string())),
                    Spanned::dummy(Pattern::Var("second".to_string())),
                    Spanned::dummy(Pattern::Var("tested".to_string())),
                ],
                preconditions: Vec::new(),
                guard: Some(Spanned::dummy(Expr::Var("tested".to_string()))),
                body_id: 0,
            },
            PatternRow {
                patterns: vec![
                    Spanned::dummy(Pattern::Wildcard),
                    Spanned::dummy(Pattern::Wildcard),
                    Spanned::dummy(Pattern::Wildcard),
                ],
                preconditions: Vec::new(),
                guard: None,
                body_id: 1,
            },
        ],
    ))
    .expect("the guard reads its third input");
    assert_eq!(
        plan.input_demand(),
        [DispatchDemand::Ignore, DispatchDemand::Ignore, DispatchDemand::Whole],
        "the plan, not reachability, records the guard's exact input read"
    );

    let mut types = Types::new();
    let first = types.type_var(TypeVarId(40));
    let second = types.type_var(TypeVarId(41));
    let tested = types.type_var(TypeVarId(42));
    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[first, second, tested]);
    let any = types.any();

    assert_eq!(
        reachable_body_ids(&plan, &reachability),
        vec![0, 1],
        "the guard and fallback both remain reachable"
    );
    for (outcome, inputs) in &reachability.outcome_inputs {
        assert_eq!(
            inputs[0], first,
            "outcome {outcome:?} must retain its first untouched variable"
        );
        assert_eq!(
            inputs[1], second,
            "outcome {outcome:?} must retain its second untouched variable"
        );
        assert!(
            types.is_equivalent(&inputs[2], &any),
            "outcome {outcome:?} must envelope only the guard's third input"
        );
    }
}

fn reachable_body_ids(plan: &PatternDispatchPlan<Ty>, reachability: &DispatchReachability) -> Vec<u32> {
    plan.outcomes
        .iter()
        .enumerate()
        .filter(|(index, _)| reachability.outcomes.binary_search(&OutcomeId(*index as u32)).is_ok())
        .map(|(_, outcome)| outcome.body_id)
        .collect()
}

#[test]
fn named_struct_field_constraints_refine_their_exact_root_and_reject_other_families() {
    use crate::compiler2::dispatch::SourcePatternResolver;
    use crate::compiler2::{ModuleId, Namespace, World};
    use crate::dispatch_matrix::pattern::pattern_dispatch_from_source_with_resolver;
    use crate::modules::identity::ModuleName;

    let mut world = World::new();
    let name = ModuleName::parse_dotted("Nested.Box").unwrap();
    let module = world.reference_module(name.clone());
    let other_module = world.reference_module(ModuleName::parse_dotted("Other.Box").unwrap());
    let mut resolver = SourcePatternResolver {
        world: &mut world,
        namespace: Namespace::default(),
        owner: ModuleId::GLOBAL,
        guard: |_world: &mut World, _callee: &crate::ast::Callee, _arity: usize| Ok(None),
    };
    let plan = pattern_dispatch_from_source_with_resolver(
        SourcePatternRows::lexical(
            1,
            vec![
                row(
                    Pattern::Tuple(vec![Spanned::dummy(Pattern::Struct {
                        module: crate::ast::ModuleTarget::Unresolved(name),
                        fields: vec![("value".into(), Spanned::dummy(Pattern::Atom("hit".into())))],
                    })]),
                    0,
                ),
                row(Pattern::Wildcard, 1),
            ],
        ),
        &mut resolver,
    )
    .unwrap();
    let hit = world.types_mut().atom_lit("hit");
    let miss = world.types_mut().atom_lit("miss");
    let values = world.types_mut().union(hit, miss);
    let fields = vec!["value".into()];
    let named = world.struct_value_ty(module, &fields, &[values]);
    let named_hit = world.struct_value_ty(module, &fields, &[hit]);
    let named_miss = world.struct_value_ty(module, &fields, &[miss]);
    let wrong = world.struct_value_ty(other_module, &fields, &[hit]);
    let plain = world.types_mut().map(&[(MapKey::Atom("value".into()), hit)]);
    let types = world.types_mut();
    for (input, expected) in [
        (named_hit, vec![0]),
        (named_miss, vec![1]),
        (wrong, vec![1]),
        (plain, vec![1]),
    ] {
        let input = types.tuple(&[input]);
        let reach = calculate_dispatch_reachability(types, &plan, &[input]);
        assert_eq!(reachable_body_ids(&plan, &reach), expected);
        assert!(!reach.fail_reachable);
    }
    let input = types.tuple(&[named]);
    let reach = calculate_dispatch_reachability(types, &plan, &[input]);
    assert_eq!(reachable_body_ids(&plan, &reach), vec![0, 1]);
    let matched_root = reach
        .outcome_inputs
        .iter()
        .find(|(outcome, _)| *outcome == OutcomeId(0))
        .unwrap()
        .1[0];
    let expected = types.tuple(&[named_hit]);
    assert!(
        types.is_equivalent(&matched_root, &expected),
        "field evidence must lift through the enclosing tuple without losing its struct tag"
    );
}

fn list_pattern(length: usize, open_tail: bool) -> Pattern {
    Pattern::List(
        (0..length).map(|_| Spanned::dummy(Pattern::Wildcard)).collect(),
        open_tail.then(|| Box::new(Spanned::dummy(Pattern::Wildcard))),
    )
}

#[test]
fn proper_list_domain_is_exhausted_by_zero_one_and_two_plus_rows() {
    let total = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![
            row(list_pattern(0, false), 0),
            row(list_pattern(1, false), 1),
            row(list_pattern(2, true), 2),
        ],
    ))
    .expect("list length partitions should compile");
    let partial = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![row(list_pattern(0, false), 0), row(list_pattern(2, true), 1)],
    ))
    .expect("partial list length partitions should compile");
    let mut types = Types::new();
    let any = types.any();
    let input = types.list(any);

    let total_reachability = calculate_dispatch_reachability(&mut types, &total, &[input]);
    let partial_reachability = calculate_dispatch_reachability(&mut types, &partial, &[input]);
    let unconstrained_reachability = calculate_dispatch_reachability(&mut types, &total, &[any]);

    assert_eq!(reachable_body_ids(&total, &total_reachability), vec![0, 1, 2]);
    assert!(!total_reachability.fail_reachable);
    assert!(partial_reachability.fail_reachable);
    assert!(
        unconstrained_reachability.fail_reachable,
        "the list partition must not consume non-list values"
    );
}

#[test]
fn bare_template_inputs_are_refined_as_runtime_values() {
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![row(Pattern::Atom("x".to_string()), 0), row(Pattern::Wildcard, 1)],
    ))
    .expect("atom patterns should compile");
    let mut types = Types::new();
    let input = types.type_var(TypeVarId(0));

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

    assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
    let atom_input = reachability
        .outcome_inputs
        .iter()
        .find_map(|(outcome, inputs)| (plan.outcome(*outcome)?.body_id == 0).then_some(inputs[0]))
        .expect("the atom outcome should retain its refined input");
    let x = types.atom_lit("x");
    assert!(types.is_equivalent(&atom_input, &x));
}

#[test]
fn nested_template_inputs_keep_their_runtime_structure() {
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![
            row(
                Pattern::Tuple(vec![
                    Spanned::dummy(Pattern::Atom("x".to_string())),
                    Spanned::dummy(Pattern::Wildcard),
                ]),
                0,
            ),
            row(Pattern::Wildcard, 1),
        ],
    ))
    .expect("tuple patterns should compile");
    let mut types = Types::new();
    let alpha = types.type_var(TypeVarId(0));
    let beta = types.type_var(TypeVarId(1));
    let input = types.tuple(&[alpha, beta]);

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

    assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
    let refined = reachability
        .outcome_inputs
        .iter()
        .find_map(|(outcome, inputs)| (plan.outcome(*outcome)?.body_id == 0).then_some(inputs[0]))
        .expect("the tuple outcome should retain its refined input");
    assert_eq!(types.max_tuple_arity(&refined), 2);
    assert!(!types.has_vars(&refined));
}

#[test]
fn nested_positive_runtime_envelope_grounds_projectable_structures() {
    let mut types = Types::new();
    let alpha = types.type_var(TypeVarId(0));
    let list = types.list(alpha);
    let map = types.map(&[(MapKey::Atom("items".to_string()), list)]);
    let input = types.tuple(&[map]);
    let envelope = types.runtime_envelope(input);
    let any = types.any();
    let list = types.list(any);
    let map = types.map(&[(MapKey::Atom("items".to_string()), list)]);
    let expected = types.tuple(&[map]);

    assert!(types.is_equivalent(&envelope, &expected));
    assert!(!types.has_vars(&envelope));
}

#[test]
fn callable_template_inputs_keep_their_callable_correlation() {
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(1, vec![row(Pattern::Wildcard, 0)]))
        .expect("wildcard patterns should compile");
    let mut types = Types::new();
    let input = types.closure_lit(crate::compiler2::types::ClosureTarget(7), Vec::new(), 2);

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

    assert_eq!(reachable_body_ids(&plan, &reachability), vec![0]);
    assert!(types.is_equivalent(&reachability.outcome_inputs[0].1[0], &input));
}

#[test]
fn ground_dispatch_inputs_are_unchanged() {
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![row(Pattern::Atom("x".to_string()), 0), row(Pattern::Wildcard, 1)],
    ))
    .expect("atom patterns should compile");
    let mut types = Types::new();
    let input = types.atom_lit("x");

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

    assert_eq!(reachable_body_ids(&plan, &reachability), vec![0]);
    assert!(types.is_equivalent(&reachability.outcome_inputs[0].1[0], &input));
}

#[test]
fn symbolic_wide_tuple_decision_chain_stays_graph_bounded() {
    let width = 16;
    let mut rows = (0..width)
        .map(|index| {
            let mut fields = (0..width)
                .map(|_| Spanned::dummy(Pattern::Wildcard))
                .collect::<Vec<_>>();
            fields[index] = Spanned::dummy(Pattern::Bool(true));
            row(Pattern::Tuple(fields), index as u32)
        })
        .collect::<Vec<_>>();
    rows.push(row(
        Pattern::Tuple((0..width).map(|_| Spanned::dummy(Pattern::Wildcard)).collect()),
        width as u32,
    ));
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(1, rows))
        .expect("wide tuple patterns should compile through the production pattern builder");
    let mut types = Types::new();
    let boolean = types.bool();
    let fields = types.repeat(boolean, width);
    let input = types.tuple(&fields);

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

    assert_eq!(
        reachable_body_ids(&plan, &reachability),
        (0..=width as u32).collect::<Vec<_>>()
    );
    assert!(!reachability.fail_reachable);
    assert!(
        reachability.visited_states <= width * 8,
        "symbolic traversal visited {} states",
        reachability.visited_states,
    );
    assert_eq!(reachability.max_root_slots, plan.input_count);
    assert!(plan.graph.subjects.len() > reachability.max_root_slots);
}

#[test]
fn negative_tuple_conjunction_remains_a_conservative_root_alternative() {
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![
            row(
                Pattern::Tuple(vec![
                    Spanned::dummy(Pattern::Atom("a".to_string())),
                    Spanned::dummy(Pattern::Wildcard),
                ]),
                0,
            ),
            row(Pattern::Wildcard, 1),
        ],
    ))
    .expect("tuple patterns should compile");
    let mut types = Types::new();
    let atom = types.atom();
    let any_pair = types.tuple(&[atom, atom]);
    let a = types.atom_lit("a");
    let any = types.any();
    let excluded = types.tuple(&[a, any]);
    let input = types.difference(any_pair, excluded);

    assert_eq!(types.projection_alternatives(input), vec![input]);

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

    assert!(reachable_body_ids(&plan, &reachability).contains(&1));
    assert!(!reachability.fail_reachable);
    assert_eq!(reachability.max_root_slots, plan.input_count);
}

#[test]
fn unresolved_negative_tuple_exclusion_keeps_both_dispatch_rows_reachable() {
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![
            row(
                Pattern::Tuple(vec![
                    Spanned::dummy(Pattern::Atom("a".to_string())),
                    Spanned::dummy(Pattern::Wildcard),
                ]),
                0,
            ),
            row(Pattern::Wildcard, 1),
        ],
    ))
    .expect("tuple patterns should compile");
    let mut types = Types::new();
    let any = types.any();
    let universe = types.tuple(&[any, any]);
    let a = types.atom_lit("a");
    let alpha = types.type_var(TypeVarId(0));
    let excluded = types.tuple(&[a, alpha]);
    let input = types.difference(universe, excluded);

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

    assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
    assert!(!reachability.fail_reachable);
}

#[test]
fn mixed_runtime_envelope_keeps_the_grounded_part_of_an_exclusion() {
    let mut types = Types::new();
    let any = types.any();
    let alpha = types.type_var(TypeVarId(0));
    let lists = types.list(any);
    let alpha_lists = types.list(alpha);
    let non_alpha_lists = types.difference(lists, alpha_lists);
    let map = types.map(&[(MapKey::Atom("items".to_string()), non_alpha_lists)]);
    let input = types.tuple(&[map]);
    let envelope = types.runtime_envelope(input);
    let non_empty_lists = types.non_empty_list(any);
    let map = types.map(&[(MapKey::Atom("items".to_string()), non_empty_lists)]);
    let expected = types.tuple(&[map]);

    assert!(types.is_equivalent(&envelope, &expected));
    assert!(!types.has_vars(&envelope));
}

#[test]
fn positive_resource_envelope_grounds_its_payload() {
    let mut types = Types::new();
    let alpha = types.type_var(TypeVarId(0));
    let input = types.resource(alpha);
    let envelope = types.runtime_envelope(input);
    let any = types.any();
    let expected = types.resource(any);

    assert!(types.is_equivalent(&envelope, &expected));
    assert!(!types.has_vars(&envelope));
}

#[test]
fn nested_resource_envelope_grounds_every_inspectable_payload() {
    let mut types = Types::new();
    let alpha = types.type_var(TypeVarId(0));
    let inner = types.resource(alpha);
    let input = types.resource(inner);
    let envelope = types.runtime_envelope(input);
    let any = types.any();
    let inner = types.resource(any);
    let expected = types.resource(inner);

    assert!(types.is_equivalent(&envelope, &expected));
    assert!(!types.has_vars(&envelope));
}

#[test]
fn negative_resource_envelope_does_not_widen_its_exclusion() {
    let mut types = Types::new();
    let any = types.any();
    let resources = types.resource(any);
    let alpha = types.type_var(TypeVarId(0));
    let alpha_resources = types.resource(alpha);
    let input = types.difference(resources, alpha_resources);
    let envelope = types.runtime_envelope(input);

    assert!(types.is_equivalent(&envelope, &resources));
    assert!(!types.has_vars(&envelope));
}

#[test]
fn resource_envelopes_contain_representative_concrete_instantiations() {
    let mut types = Types::new();
    let alpha_id = TypeVarId(0);
    let alpha = types.type_var(alpha_id);
    let resource = types.resource(alpha);
    let nested = types.resource(resource);
    let any = types.any();
    let resources = types.resource(any);
    let excluded = types.difference(resources, resource);
    let templates = [resource, nested, excluded];
    let envelopes = templates.map(|template| types.runtime_envelope(template));
    let int = types.int();
    let atom = types.atom();
    let list = types.list(int);

    for witness in [int, atom, list] {
        let mut sigma = Sigma::new();
        sigma.insert(alpha_id, witness);
        for (template, envelope) in templates.iter().zip(envelopes.iter()) {
            let instantiated = types.instantiate(template, &sigma);
            assert!(types.is_subtype(&instantiated, envelope));
        }
    }
}

#[test]
fn cofinite_variable_double_negation_preserves_possible_tuple_values() {
    let mut types = Types::new();
    let alpha = types.type_var(TypeVarId(0));
    let any = types.any();
    let not_alpha = types.difference(any, alpha);
    let universe = types.tuple(&[any]);
    let excluded = types.tuple(&[not_alpha]);
    let input = types.difference(universe, excluded);
    let envelope = types.runtime_envelope(input);

    assert!(types.is_equivalent(&envelope, &universe));
    assert!(!types.is_empty(&envelope));
}

#[test]
fn finite_negative_variable_branch_preserves_mixed_ground_axes() {
    let mut types = Types::new();
    let alpha = types.type_var(TypeVarId(0));
    let int = types.int();
    let alpha_or_int = types.union(alpha, int);
    let any = types.any();
    let universe = types.tuple(&[any]);
    let excluded = types.tuple(&[alpha_or_int]);
    let input = types.difference(universe, excluded);
    let envelope = types.runtime_envelope(input);
    let excluded = types.tuple(&[int]);
    let expected = types.difference(universe, excluded);

    assert!(types.is_equivalent(&envelope, &expected));
}

#[test]
fn positive_cofinite_variable_branch_remains_a_runtime_top() {
    let mut types = Types::new();
    let alpha = types.type_var(TypeVarId(0));
    let any = types.any();
    let not_alpha = types.difference(any, alpha);
    let envelope = types.runtime_envelope(not_alpha);

    assert!(types.is_equivalent(&envelope, &any));
}

#[test]
fn saturated_variable_axis_without_exclusions_remains_ordinary_top() {
    let mut types = Types::new();
    let any = types.any();
    let universe = types.tuple(&[any]);
    let input = types.difference(universe, universe);
    let envelope = types.runtime_envelope(input);

    assert!(types.is_empty(&envelope));
}

#[test]
fn cofinite_variable_double_negation_preserves_possible_resource_values() {
    let mut types = Types::new();
    let alpha = types.type_var(TypeVarId(0));
    let any = types.any();
    let not_alpha = types.difference(any, alpha);
    let resources = types.resource(any);
    let excluded = types.resource(not_alpha);
    let input = types.difference(resources, excluded);
    let envelope = types.runtime_envelope(input);

    assert!(types.is_equivalent(&envelope, &resources));
    assert!(!types.is_empty(&envelope));
}

#[test]
fn cofinite_double_negation_envelopes_contain_concrete_instantiations() {
    let mut types = Types::new();
    let alpha_id = TypeVarId(0);
    let alpha = types.type_var(alpha_id);
    let any = types.any();
    let not_alpha = types.difference(any, alpha);
    let tuple_universe = types.tuple(&[any]);
    let tuple_excluded = types.tuple(&[not_alpha]);
    let tuple_template = types.difference(tuple_universe, tuple_excluded);
    let resource_universe = types.resource(any);
    let resource_excluded = types.resource(not_alpha);
    let resource_template = types.difference(resource_universe, resource_excluded);
    let templates = [tuple_template, resource_template];
    let envelopes = templates.map(|template| types.runtime_envelope(template));
    let int = types.int();
    let atom = types.atom();
    let list = types.list(int);

    for witness in [int, atom, list] {
        let mut sigma = Sigma::new();
        sigma.insert(alpha_id, witness);
        for (template, envelope) in templates.iter().zip(envelopes.iter()) {
            let instantiated = types.instantiate(template, &sigma);
            assert!(types.is_subtype(&instantiated, envelope));
        }
    }
}

#[test]
fn unresolved_resource_payload_keeps_matching_type_precondition_reachable() {
    let mut types = Types::new();
    let int = types.int();
    let resource_int = types.resource(int);
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![
            PatternRow {
                patterns: vec![Spanned::dummy(Pattern::Wildcard)],
                preconditions: vec![(PatternSubjectRef::Input(0), resource_int)],
                guard: None,
                body_id: 0,
            },
            row(Pattern::Wildcard, 1),
        ],
    ))
    .expect("resource preconditions should compile");
    let alpha = types.type_var(TypeVarId(0));
    let input = types.resource(alpha);

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

    assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
    assert!(!reachability.fail_reachable);
}

#[test]
fn mixed_axis_union_remains_conservative_through_tuple_projection() {
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        1,
        vec![
            row(
                Pattern::Tuple(vec![
                    Spanned::dummy(Pattern::Atom("a".to_string())),
                    Spanned::dummy(Pattern::Atom("x".to_string())),
                ]),
                0,
            ),
            row(Pattern::Wildcard, 1),
        ],
    ))
    .expect("tuple patterns should compile");
    let mut types = Types::new();
    let a = types.atom_lit("a");
    let x = types.atom_lit("x");
    let pair = types.tuple(&[a, x]);
    let other = types.atom_lit("other");
    let input = types.union(pair, other);

    assert_eq!(types.projection_alternatives(input), vec![input]);

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[input]);

    assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
    assert!(!reachability.fail_reachable);
    assert_eq!(reachability.max_root_slots, plan.input_count);
}

/// fz-f98.14.11 — a slot no test looks at comes back exactly as it went
/// in. The runtime envelope answers "what could this be at runtime", which
/// is `any` for a type variable, and that is right for deciding which
/// clauses a value can reach. But the refined inputs are also what types
/// the clause's parameters, and there a variable means NOT-YET-KNOWN, not
/// "anything" -- graduating it to `any` there loses the binding the
/// fixpoint is still working out, and cumulative joins never take it back.
/// A slot that appears in no test cannot change any test's outcome, so it
/// needs no envelope at all.
#[test]
fn a_slot_no_test_looks_at_keeps_its_type_variable() {
    let plan = pattern_dispatch_from_source(SourcePatternRows::lexical(
        2,
        vec![
            row2(Pattern::Atom("x".to_string()), Pattern::Wildcard, 0),
            row2(Pattern::Wildcard, Pattern::Wildcard, 1),
        ],
    ))
    .expect("atom patterns should compile");
    let mut types = Types::new();
    let tested = types.type_var(TypeVarId(0));
    let untested = types.type_var(TypeVarId(1));

    let reachability = calculate_dispatch_reachability(&mut types, &plan, &[tested, untested]);

    assert_eq!(reachable_body_ids(&plan, &reachability), vec![0, 1]);
    assert!(
        !reachability.outcome_inputs.is_empty(),
        "both clauses should be reachable with refined inputs"
    );
    let any = types.any();
    for (outcome, inputs) in &reachability.outcome_inputs {
        assert_eq!(
            inputs[1],
            untested,
            "outcome {outcome:?}: the untested slot should keep its variable, got `{}`",
            types.display(&inputs[1])
        );
        assert!(
            !types.is_equivalent(&inputs[1], &any),
            "outcome {outcome:?}: the untested slot must not graduate to any"
        );
    }
}

#[test]
fn nil_predicates_use_the_atom_type_and_map_key() {
    let mut types = Types::new();
    let nil = predicate_target(&mut types, &Region::Equal(ComparisonValue::Const(GroundValue::Nil)))
        .expect("nil equality is type-representable");
    assert!(types.is_nil(&nil.ty));

    let required = predicate_target(&mut types, &Region::MapKeyPresent { key: GroundValue::Nil })
        .expect("nil is the atom key :nil");
    let any = types.any();
    let expected = types.map(&[(crate::ground_value::MapKey::Atom("nil".to_string()), any)]);
    assert!(types.is_equivalent(&required.ty, &expected));
}
