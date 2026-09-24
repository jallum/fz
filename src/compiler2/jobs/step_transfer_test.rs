use super::*;

fn run_step(world: &mut World, step: &LoweredStep, values: &mut SemanticValues) -> (Vec<FactKey>, HashSet<FactKey>) {
    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    evaluate_step(world, step, values, &mut reads, &mut waits).unwrap();
    (reads, waits)
}

fn value(index: u32) -> ValueId {
    ValueId::from_u32(index)
}

#[test]
fn nested_tuple_assertion_preserves_refinement_ancestors_and_unrelated_pending_values() {
    let mut world = World::new();
    let any = world.types_mut().any();
    let int = world.types_mut().int();
    let inner_ty = world.types_mut().tuple(&[any]);
    let outer_ty = world.types_mut().tuple(&[inner_ty]);
    let (outer, inner, field, witness, unrelated) = (value(0), value(1), value(2), value(3), value(4));
    let mut values = SemanticValues::default();
    for (id, ty) in [(outer, outer_ty), (inner, inner_ty), (field, any), (witness, int)] {
        values.insert(id, ty);
    }
    values.insert_value(unrelated, SemanticValue::pending());
    values.assert_tuple(outer, 1);
    values.assert_tuple(inner, 1);
    values.project_tuple_field(inner, outer, 0);
    values.project_tuple_field(field, inner, 0);
    let step = LoweredStep::AssertSame {
        source: field,
        value: witness,
    };
    let inputs = step_inputs(&step, &values);
    let delta = step_delta(&mut world, &step, &inputs, &mut Vec::new(), &mut HashSet::new()).unwrap();
    assert_eq!(
        delta.types.keys().copied().collect::<HashSet<_>>(),
        HashSet::from([outer, inner, field])
    );
    assert!(
        delta.tuple_fields.is_empty(),
        "unchanged projection history belongs to the existing scope"
    );
    values.apply_delta(delta);
    let narrowed_inner = world.types_mut().tuple(&[int]);
    let narrowed_outer = world.types_mut().tuple(&[narrowed_inner]);
    assert_eq!(value_ty(&values, field), Some(int));
    assert_eq!(value_ty(&values, inner), Some(narrowed_inner));
    assert_eq!(value_ty(&values, outer), Some(narrowed_outer));
    assert!(values.contains_key(&unrelated));
    assert_eq!(value_ty(&values, unrelated), None);
    assert_eq!(values.tuple_field(field).unwrap().source, inner);
    assert_eq!(values.tuple_field(inner).unwrap().source, outer);
}

#[test]
fn tuple_assertion_and_projection_keep_metadata_without_observing_a_pending_value() {
    let mut world = World::new();
    let (source, field) = (value(0), value(1));
    let mut values = SemanticValues::default();
    values.insert_value(source, SemanticValue::pending());
    run_step(&mut world, &LoweredStep::AssertTuple { source, arity: 2 }, &mut values);
    run_step(
        &mut world,
        &LoweredStep::TupleField {
            value: field,
            source,
            index: 1,
        },
        &mut values,
    );
    assert_eq!(values.tuple_arities.get(&source), Some(&2));
    assert!(values.contains_key(&field));
    assert_eq!(value_ty(&values, field), None);
    let projection = values.tuple_field(field).unwrap();
    assert_eq!((projection.source, projection.index, projection.arity), (source, 1, 2));
}

#[test]
fn a_primitive_result_does_not_overwrite_its_operands_callable_surfaces() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let surface = ActivationSignature {
        inputs: vec![int].into_boxed_slice(),
        result: int,
    };
    let (input, output, unrelated) = (value(0), value(1), value(2));
    let mut values = SemanticValues::default();
    values.insert_value(input, SemanticValue::callable(int, surface.clone()));
    values.insert_value(unrelated, SemanticValue::pending());
    run_step(
        &mut world,
        &LoweredStep::UnaryOp {
            value: output,
            op: UnOp::Neg,
            input,
        },
        &mut values,
    );
    assert_eq!(value_ty(&values, output), Some(int));
    assert!(values.get(&output).unwrap().callable_surfaces.is_empty());
    assert_eq!(values.get(&input).unwrap().callable_surfaces, BTreeSet::from([surface]));
    assert!(values.contains_key(&unrelated));
}

#[test]
fn an_absent_operand_and_a_pending_operand_do_not_invent_primitive_results() {
    let mut world = World::new();
    let (input, output) = (value(0), value(1));
    let step = LoweredStep::UnaryOp {
        value: output,
        op: UnOp::Neg,
        input,
    };
    let mut values = SemanticValues::default();
    run_step(&mut world, &step, &mut values);
    assert!(!values.contains_key(&output));
    values.insert_value(input, SemanticValue::pending());
    run_step(&mut world, &step, &mut values);
    assert!(!values.contains_key(&output));
}

#[test]
fn struct_assertion_forwards_its_existing_fact_wait() {
    let mut world = World::new();
    let module = world.reference_child_module(ModuleId::GLOBAL, "WaitingStruct");
    let source = value(0);
    let any = world.types_mut().any();
    let mut values = SemanticValues::default();
    values.insert(source, any);
    let (reads, waits) = run_step(&mut world, &LoweredStep::AssertStruct { source, module }, &mut values);
    assert!(reads.is_empty());
    assert_eq!(waits, HashSet::from([FactKey::StructDefined(module)]));
    world.define_struct_def(
        module,
        crate::compiler2::structdef::StructDef {
            fields: vec!["field".into()],
            span: Span::DUMMY,
        },
    );
    values.insert(source, any);
    let (reads, waits) = run_step(&mut world, &LoweredStep::AssertStruct { source, module }, &mut values);
    assert_eq!(reads, vec![FactKey::StructDefined(module)]);
    assert!(
        waits.is_empty(),
        "an arrived schema becomes a read, just as in the original evaluator"
    );
}

#[test]
fn replacing_a_source_operation_recomputes_the_same_result_position() {
    let mut world = World::new();
    let (input, output) = (value(0), value(1));
    let int = world.types_mut().int();
    let mut values = SemanticValues::default();
    values.insert(input, int);
    run_step(
        &mut world,
        &LoweredStep::UnaryOp {
            value: output,
            op: UnOp::Neg,
            input,
        },
        &mut values,
    );
    assert_eq!(value_ty(&values, output), Some(int));
    run_step(
        &mut world,
        &LoweredStep::UnaryOp {
            value: output,
            op: UnOp::Not,
            input,
        },
        &mut values,
    );
    assert_eq!(value_ty(&values, output), Some(world.types_mut().bool()));
}

#[test]
fn a_step_delta_contains_only_its_result_and_excludes_unread_scope_values() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let (input, output, unrelated) = (value(0), value(1), value(2));
    let surface = ActivationSignature {
        inputs: vec![int].into_boxed_slice(),
        result: int,
    };
    let mut scope = SemanticValues::default();
    scope.insert_value(input, SemanticValue::callable(int, surface));
    scope.insert_value(unrelated, SemanticValue::pending());
    scope.assert_tuple(unrelated, 2);
    let step = LoweredStep::UnaryOp {
        value: output,
        op: UnOp::Neg,
        input,
    };
    let inputs = step_inputs(&step, &scope);
    assert_eq!(inputs.types.len(), 1);
    assert!(inputs.get(&input).unwrap().callable_surfaces.is_empty());
    assert!(inputs.tuple_arities.is_empty());
    let delta = step_delta(&mut world, &step, &inputs, &mut Vec::new(), &mut HashSet::new()).unwrap();
    assert_eq!(delta.types.len(), 1);
    assert_eq!(value_ty(&delta, output), Some(int));
    assert!(!delta.contains_key(&input));
    assert!(!delta.contains_key(&unrelated));
    let later = world.types_mut().bool();
    scope.insert(unrelated, later);
    scope.apply_delta(delta);
    assert_eq!(value_ty(&scope, unrelated), Some(later));
    assert_eq!(scope.tuple_arities.get(&unrelated), Some(&2));
    assert_eq!(scope.get(&input).unwrap().callable_surfaces.len(), 1);
}

#[test]
fn a_noop_bitstring_check_reads_no_semantic_value_and_returns_no_delta() {
    let mut world = World::new();
    let reader = value(0);
    let mut scope = SemanticValues::default();
    scope.insert_value(reader, SemanticValue::pending());
    let step = LoweredStep::AssertBitstringDone { reader };
    let inputs = step_inputs(&step, &scope);
    assert!(inputs.types.is_empty());
    let delta = step_delta(&mut world, &step, &inputs, &mut Vec::new(), &mut HashSet::new()).unwrap();
    assert!(delta.types.is_empty());
    assert!(delta.tuple_arities.is_empty());
    assert!(delta.tuple_fields.is_empty());
}

#[test]
fn literal_map_keys_do_not_read_their_runtime_value_slot() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let (base, key, output) = (value(0), value(1), value(2));
    let map = world.types_mut().map(&[(MapKey::Atom("field".into()), int)]);
    let mut values = SemanticValues::default();
    values.insert(base, map);
    values.insert_value(key, SemanticValue::pending());
    let step = LoweredStep::MapIndex {
        value: output,
        base,
        key: LoweredMapKey {
            value: key,
            literal: Some(GroundValue::Atom("field".into())),
        },
    };
    let inputs = step_inputs(&step, &values);
    assert_eq!(inputs.types.keys().copied().collect::<Vec<_>>(), [base]);
    run_step(&mut world, &step, &mut values);
    assert_eq!(value_ty(&values, output), Some(int));
    assert_eq!(value_ty(&values, key), None);
}

#[test]
fn dynamic_map_keys_read_types_but_map_items_and_update_bases_keep_callable_surfaces() {
    let mut world = World::new();
    let atom = world.types_mut().atom_lit("field");
    let int = world.types_mut().int();
    let map = world.types_mut().map(&[]);
    let (key, item, base, output) = (value(0), value(1), value(2), value(3));
    let surface = |ty| ActivationSignature {
        inputs: vec![ty].into_boxed_slice(),
        result: ty,
    };
    let (key_surface, item_surface, base_surface) = (surface(atom), surface(int), surface(map));
    let mut scope = SemanticValues::default();
    scope.insert_value(key, SemanticValue::callable(atom, key_surface.clone()));
    scope.insert_value(item, SemanticValue::callable(int, item_surface.clone()));
    scope.insert_value(base, SemanticValue::callable(map, base_surface.clone()));
    for update in [false, true] {
        for aliased_item in [false, true] {
            let entries = vec![(
                LoweredMapKey {
                    value: key,
                    literal: None,
                },
                if aliased_item { key } else { item },
            )];
            let step = if update {
                LoweredStep::MapUpdate {
                    value: output,
                    base,
                    entries,
                }
            } else {
                LoweredStep::Map {
                    value: output,
                    entries,
                    quoted_span: None,
                }
            };
            let inputs = step_inputs(&step, &scope);
            assert_eq!(
                inputs.get(&key).unwrap().callable_surfaces.contains(&key_surface),
                aliased_item,
                "a dynamic key reads its Ty; the same ValueId also used as an item must retain its surface"
            );
            assert_eq!(value_ty(&inputs, key), Some(atom));
            let delta = step_delta(&mut world, &step, &inputs, &mut Vec::new(), &mut HashSet::new()).unwrap();
            let mut expected = BTreeSet::from([if aliased_item {
                key_surface.clone()
            } else {
                item_surface.clone()
            }]);
            if update {
                expected.insert(base_surface.clone());
            }
            assert_eq!(delta.get(&output).unwrap().callable_surfaces, expected);
            assert!(
                !delta.contains_key(&key),
                "projecting an input does not rewrite its caller-owned surfaces"
            );
        }
    }
}

#[test]
fn lambda_transfer_keeps_capture_order_and_inherited_callable_surfaces() {
    let mut world = World::new();
    let function = world.reference_function(ModuleId::GLOBAL, "capturing", 1);
    let int = world.types_mut().int();
    let atom = world.types_mut().atom_lit("left");
    let inherited = ActivationSignature {
        inputs: vec![int].into_boxed_slice(),
        result: atom,
    };
    let (left, right, output) = (value(0), value(1), value(2));
    let mut values = SemanticValues::default();
    values.insert_value(left, SemanticValue::callable(atom, inherited.clone()));
    values.insert(right, int);
    for (captures, expected) in [
        (vec![left, right], vec![atom, int]),
        (vec![right, left], vec![int, atom]),
    ] {
        run_step(
            &mut world,
            &LoweredStep::Lambda {
                value: output,
                function,
                captures,
            },
            &mut values,
        );
        let result = values.get(&output).unwrap();
        assert!(result.callable_surfaces.contains(&inherited));
        let clauses = world.types_mut().callable_value_clauses(&result.ty().unwrap()).unwrap();
        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].closure.as_ref().unwrap().captures, expected);
    }
}
