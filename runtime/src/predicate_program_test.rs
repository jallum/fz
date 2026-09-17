use super::*;
use crate::any_value::{AnyValue, AnyValueRef, ValueKind};
use crate::heap::{Schema, SchemaRegistry};
use crate::process::Process;
use std::cell::RefCell;
use std::rc::Rc;

fn with_process<R>(f: impl FnOnce(&mut Process) -> R) -> R {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut process = Process::new(schemas);
    f(&mut process)
}

fn binary_tree_program() -> RuntimePredicateProgram {
    RuntimePredicateProgram::new(
        0,
        vec![
            RuntimePredicateNode::any_of(0, 2),
            RuntimePredicateNode::tag(ValueKind::INT),
            RuntimePredicateNode::tuple(2, 2, 2),
        ],
        vec![1, 2, 0, 0],
    )
    .expect("well-formed regular tree predicate")
}

fn pair(process: &mut Process, schema: u32, left: AnyValueRef, right: AnyValueRef) -> AnyValueRef {
    let object = process.heap.alloc_struct(schema);
    let object_ref = AnyValueRef::from_heap_object(ValueKind::STRUCT, object).expect("tuple reference");
    unsafe {
        process
            .heap
            .write_struct_field_ref(object_ref, 0, left)
            .expect("tuple left field");
        process
            .heap
            .write_struct_field_ref(object_ref, 8, right)
            .expect("tuple right field");
    }
    object_ref
}

#[test]
fn regular_program_matches_deep_finite_branching_without_a_depth_budget() {
    with_process(|process| {
        let program = binary_tree_program();
        let schema = process.heap.register_schema(Schema::tuple_of_arity(2));
        let leaf = process.heap.box_any_value_ref(AnyValue::int(0));
        let mut value = leaf;
        for _ in 0..20_000 {
            value = pair(process, schema, value, leaf);
        }

        assert!(program.matches(process, value));
    });
}

#[test]
fn regular_program_rejects_one_bad_leaf_after_a_deep_branching_descent() {
    with_process(|process| {
        let program = binary_tree_program();
        let schema = process.heap.register_schema(Schema::tuple_of_arity(2));
        let int = process.heap.box_any_value_ref(AnyValue::int(0));
        let atom = process.heap.box_any_value_ref(AnyValue::atom(7));
        let mut value = atom;
        for _ in 0..4_000 {
            value = pair(process, schema, int, value);
        }

        assert!(!program.matches(process, value));
    });
}

#[test]
fn program_owner_keeps_its_static_tables_alive_for_each_evaluator_handle() {
    with_process(|process| {
        let program = binary_tree_program();
        let retained = program.clone();
        let static_data = retained.static_data();
        drop(program);
        let int = process.heap.box_any_value_ref(AnyValue::int(0));

        assert!(retained.matches(process, int));
        assert!(static_data.matches(process, int).expect("owned static view"));
    });
}

#[test]
fn static_abi_evaluator_agrees_with_the_owned_program() {
    with_process(|process| {
        let program = binary_tree_program();
        let schema = process.heap.register_schema(Schema::tuple_of_arity(2));
        let int = process.heap.box_any_value_ref(AnyValue::int(0));
        let value = pair(process, schema, int, int);
        let static_data = program.static_data();

        let through_c_abi =
            unsafe { fz_runtime_predicate_program_matches(process, value.raw_word(), static_data.as_ptr()) != 0 };
        assert_eq!(program.matches(process, value), through_c_abi);
    });
}

#[test]
fn an_unproductive_cycle_does_not_succeed_while_it_is_being_visited() {
    with_process(|process| {
        let program = RuntimePredicateProgram::new(0, vec![RuntimePredicateNode::any_of(0, 1)], vec![0])
            .expect("well-formed unproductive cycle");
        let int = process.heap.box_any_value_ref(AnyValue::int(0));

        assert!(!program.matches(process, int));
    });
}
