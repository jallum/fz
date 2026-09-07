use super::*;
use crate::compiler2::artifact::{BackendCallableReturn, BackendConstructionMemberAdapter};
use crate::compiler2::transport::{BoundaryId, CallableId, ShapeDescr};
use crate::compiler2::{ActivationKey, ExecutableNeed, RootId, World};

fn key(world: &mut World, name: &str) -> ExecutableKey {
    let function = world.reference_function(ModuleId::GLOBAL, name, 0);
    ExecutableKey {
        activation: ActivationKey::from_inputs(RootId::for_test(0), function, &[], world.types_mut()),
        need: ExecutableNeed::Value,
    }
}

fn backend(world: &mut World, key: &ExecutableKey, atoms: &[&str]) -> Rc<BackendExecutable> {
    let nothing = world.intern_shape(ShapeDescr::Nothing);
    let mut backend = BackendExecutable::for_test(key.clone(), world.types_mut().none(), nothing);
    backend.atom_names = atoms.iter().map(|atom| Rc::new((*atom).to_string())).collect();
    Rc::new(backend)
}

fn atom(program: &BackendProgram, name: &str) -> Rc<String> {
    program
        .atom_names
        .iter()
        .find(|atom| atom.as_str() == name)
        .cloned()
        .expect("published atom")
}

fn atom_order(program: &BackendProgram) -> Vec<&str> {
    program.atom_names.iter().map(|atom| atom.as_str()).collect()
}

fn with_wrapper(backend: &Rc<BackendExecutable>) -> Rc<BackendExecutable> {
    let wrapper = BackendConstructionWrapper {
        identity: backend.abi.transport.return_position.clone(),
        callable: CallableId::for_test(0),
        captures: Box::default(),
        call_arity: 0,
        return_form: BackendCallableReturn::Absent,
        members: vec![BackendConstructionMemberAdapter {
            boundary: BoundaryId::for_test(0),
            surface_inputs: Box::default(),
            surface_arg_shapes: Box::default(),
            target: backend.key.clone(),
            capture_semantic_inputs: Box::default(),
            surface_semantic_inputs: Box::default(),
            target_inputs: Box::default(),
            target_return: backend.abi.return_layout.clone(),
        }]
        .into_boxed_slice(),
        selection: None,
    };
    let mut backend = backend.as_ref().clone();
    backend.construction_wrappers = vec![Rc::new(wrapper)].into_boxed_slice();
    Rc::new(backend)
}

#[test]
fn replacing_one_executable_retains_its_equal_atom_and_wrapper_contributions() {
    let mut world = World::new();
    let owner = key(&mut world, "owner");
    let initial = with_wrapper(&backend(&mut world, &owner, &["retained"]));
    let mut program = BackendProgram::empty(owner.clone());
    program.reconcile_executables(vec![(owner.clone(), Some(initial.clone()))], world.types());
    let before = program.clone();
    let retained_atom = atom(&before, "retained");
    let retained_wrapper = before.construction_wrappers().first().unwrap().clone();
    let next = with_wrapper(&backend(&mut world, &owner, &["retained", "added"]));
    assert!(!Rc::ptr_eq(&initial.atom_names[0], &next.atom_names[0]));
    assert!(!Rc::ptr_eq(&retained_wrapper, &next.construction_wrappers[0]));
    program.reconcile_executables(vec![(owner.clone(), Some(next.clone()))], world.types());
    assert!(Rc::ptr_eq(&retained_atom, &atom(&program, "retained")));
    assert!(Rc::ptr_eq(
        &retained_wrapper,
        program.construction_wrappers().first().unwrap()
    ));
    assert!(Rc::ptr_eq(program.executable(&owner, world.types()).unwrap(), &next));
    assert!(Rc::ptr_eq(before.executable(&owner, world.types()).unwrap(), &initial));
    assert_eq!(atom_order(&before), ["retained"]);
    assert_eq!(atom_order(&program), ["retained", "added"]);
}

#[test]
fn inserting_and_withdrawing_an_earlier_atom_owner_preserves_the_published_allocation() {
    let mut world = World::new();
    let early = key(&mut world, "early");
    let late = key(&mut world, "late");
    assert!(early.semantic_cmp(&late, world.types()).is_lt());
    let late_body = backend(&mut world, &late, &["shared"]);
    let early_body = backend(&mut world, &early, &["prefix", "shared"]);
    let mut program = BackendProgram::empty(late.clone());
    program.reconcile_executables(vec![(late.clone(), Some(late_body))], world.types());
    let before = program.clone();
    let canonical = atom(&before, "shared");
    program.reconcile_executables(vec![(early.clone(), Some(early_body))], world.types());
    let both = program.clone();
    assert_eq!(atom_order(&both), ["prefix", "shared"]);
    assert!(Rc::ptr_eq(&canonical, &atom(&both, "shared")));
    program.reconcile_executables(vec![(early, None)], world.types());
    assert_eq!(atom_order(&program), ["shared"]);
    assert!(Rc::ptr_eq(&canonical, &atom(&program, "shared")));
    assert_eq!(atom_order(&before), ["shared"]);
    assert_eq!(atom_order(&both), ["prefix", "shared"]);
}

#[test]
fn swapping_local_atom_occurrences_keeps_the_root_canonical_allocations() {
    let mut world = World::new();
    let owner = key(&mut world, "owner");
    let mut program = BackendProgram::empty(owner.clone());
    let initial = backend(&mut world, &owner, &["left", "right"]);
    program.reconcile_executables(vec![(owner.clone(), Some(initial))], world.types());
    let before = program.clone();
    let left = atom(&before, "left");
    let right = atom(&before, "right");
    let swapped = backend(&mut world, &owner, &["right", "left"]);
    program.reconcile_executables(vec![(owner, Some(swapped))], world.types());
    assert_eq!(atom_order(&program), ["right", "left"]);
    assert!(Rc::ptr_eq(&left, &atom(&program, "left")));
    assert!(Rc::ptr_eq(&right, &atom(&program, "right")));
    assert_eq!(atom_order(&before), ["left", "right"]);
}

#[test]
fn swapping_occurrences_uses_the_root_atom_allocation_not_the_replaced_body_allocation() {
    let mut world = World::new();
    let early = key(&mut world, "early");
    let late = key(&mut world, "late");
    let mut program = BackendProgram::empty(early.clone());
    let first = backend(&mut world, &early, &["left", "right"]);
    program.reconcile_executables(vec![(early.clone(), Some(first))], world.types());
    let canonical = program.clone();
    let late_body = backend(&mut world, &late, &["left", "right"]);
    assert!(!Rc::ptr_eq(&atom(&canonical, "left"), &late_body.atom_names[0]));
    program.reconcile_executables(vec![(late.clone(), Some(late_body))], world.types());
    program.reconcile_executables(vec![(early, None)], world.types());
    let before_swap = program.clone();
    let swapped = backend(&mut world, &late, &["right", "left"]);
    program.reconcile_executables(vec![(late, Some(swapped))], world.types());
    for name in ["left", "right"] {
        assert!(Rc::ptr_eq(&atom(&canonical, name), &atom(&before_swap, name)));
        assert!(
            Rc::ptr_eq(&atom(&canonical, name), &atom(&program, name)),
            "an occurrence move must preserve the root's canonical {name} allocation"
        );
    }
    assert_eq!(atom_order(&canonical), ["left", "right"]);
    assert_eq!(atom_order(&before_swap), ["left", "right"]);
    assert_eq!(atom_order(&program), ["right", "left"]);
}

#[test]
fn transferring_an_atom_between_executables_in_one_transaction_preserves_its_allocation() {
    let mut world = World::new();
    let old_owner = key(&mut world, "old_owner");
    let new_owner = key(&mut world, "new_owner");
    let mut program = BackendProgram::empty(old_owner.clone());
    let initial = backend(&mut world, &old_owner, &["transferred"]);
    program.reconcile_executables(vec![(old_owner.clone(), Some(initial))], world.types());
    let before = program.clone();
    let canonical = atom(&before, "transferred");
    let new_body = backend(&mut world, &new_owner, &["transferred"]);
    program.reconcile_executables(
        vec![(old_owner.clone(), None), (new_owner.clone(), Some(new_body))],
        world.types(),
    );
    assert!(Rc::ptr_eq(&canonical, &atom(&program, "transferred")));
    assert!(program.executable(&old_owner, world.types()).is_none());
    assert!(program.executable(&new_owner, world.types()).is_some());
    assert!(before.executable(&old_owner, world.types()).is_some());
    assert!(before.executable(&new_owner, world.types()).is_none());
    assert_eq!(atom_order(&before), ["transferred"]);
}

#[test]
fn a_real_same_body_edit_retains_its_equal_atom_and_callable_wrapper() {
    use crate::compiler2::{CodeSubmission, Compiler2, RootSubmission};
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::capture::Capture::new();
    diagnostics.install(&tel, &[]);
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(Box::new(fz_runtime::output::NullOutput));
    let source = |result| {
        format!("fn leaf(x), do: x + 1\nfn main() do\n  dbg(:retained)\n  f = &leaf/1\n  dbg(f)\n  {result}\nend\n")
    };
    compiler.submit_code(CodeSubmission {
        name: Some("same_body_contributions.fz".to_string()),
        text: source(1),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(
        compiler.run_root_interp(root),
        Ok(1),
        "{:?}",
        diagnostics.last(&["fz", "diag", "error"])
    );
    let before = compiler.retained_backend_program(root);
    let retained_atom = atom(&before, "retained");
    let wrapper = before
        .construction_wrappers()
        .iter()
        .find(|wrapper| wrapper.identity.executable().activation.function == before.entry().activation.function)
        .expect("main must publish its boxed function-reference wrapper")
        .clone();
    compiler.submit_code(CodeSubmission {
        name: Some("same_body_contributions.fz".to_string()),
        text: source(2),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(2));
    let after = compiler.retained_backend_program(root);
    assert!(!Rc::ptr_eq(&before, &after));
    assert!(Rc::ptr_eq(&retained_atom, &atom(&after, "retained")));
    let retained_wrapper = after
        .construction_wrappers()
        .iter()
        .find(|candidate| candidate.identity == wrapper.identity)
        .expect("the same function-reference position remains reached");
    assert_eq!(wrapper.as_ref(), retained_wrapper.as_ref());
    assert!(Rc::ptr_eq(&wrapper, retained_wrapper));
    assert!(Rc::ptr_eq(&retained_atom, &atom(&before, "retained")));
}

fn schema_allocations(program: &BackendProgram, name: &str) -> (Rc<String>, Rc<Vec<String>>) {
    program
        .struct_schemas
        .entries()
        .find(|(candidate, _)| candidate.as_str() == name)
        .map(|(name, fields)| (Rc::clone(name), Rc::clone(fields)))
        .expect("reached schema must be packaged")
}

#[test]
fn a_real_leaf_edit_retains_schema_allocations_without_schema_work() {
    use crate::compiler2::pull::{ProductKey, ProductRequestId, PullOutcome};
    use crate::compiler2::{CodeSubmission, Compiler2, RootSubmission};
    use std::cell::RefCell;

    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let evaluations = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&evaluations);
    tel.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
        &["fz", "compiler2", "pull", "product", "evaluated"],
        move |_, _, _, key, _, _| {
            if matches!(key, ProductKey::StructSchema(_)) {
                observed.borrow_mut().push(key.clone());
            }
        },
    );
    let mut compiler = Compiler2::new(tel);
    compiler.set_output(Box::new(fz_runtime::output::NullOutput));
    compiler.submit_code(CodeSubmission {
        name: Some("schema_contributions.fz".to_string()),
        text: concat!(
            "defmodule Item do\n  defstruct [:value]\nend\n",
            "defmodule Other do\n  defstruct [:flag]\nend\n",
            "fn leaf(), do: 1\n",
            "fn main() do\n  dbg(%Other{flag: 0})\n  item = %Item{value: leaf()}\n  item.value\nend\n",
        )
        .to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(1));
    let item = compiler.world_mut().reference_module("Item");
    let other = compiler.world_mut().reference_module("Other");
    let item_key = ProductKey::StructSchema(item);
    let other_key = ProductKey::StructSchema(other);
    let item_generation = compiler
        .retained_product_generation(root, &item_key)
        .expect("Item schema product");
    let other_generation = compiler
        .retained_product_generation(root, &other_key)
        .expect("Other schema product");
    let before = compiler.retained_backend_program(root);
    let item_allocations = schema_allocations(&before, "Item");
    let other_allocations = schema_allocations(&before, "Other");
    evaluations.borrow_mut().clear();

    compiler.submit_code(CodeSubmission {
        name: Some("schema_contributions.fz".to_string()),
        text: "fn leaf(), do: 2\n".to_string(),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(2));
    let leaf_edited = compiler.retained_backend_program(root);
    for (name, (old_name, old_fields)) in [("Item", &item_allocations), ("Other", &other_allocations)] {
        let (new_name, new_fields) = schema_allocations(&leaf_edited, name);
        assert!(Rc::ptr_eq(old_name, &new_name));
        assert!(Rc::ptr_eq(old_fields, &new_fields));
    }
    assert!(
        evaluations.borrow().is_empty(),
        "a leaf body edit reads no changed schema definition"
    );
    assert_eq!(
        compiler.retained_product_generation(root, &item_key),
        Some(item_generation)
    );
    assert_eq!(
        compiler.retained_product_generation(root, &other_key),
        Some(other_generation)
    );
}

#[test]
fn a_published_schema_edit_moves_only_its_exact_retained_contribution() {
    use crate::compiler2::drive::{ExecutionContext, JobEffects};
    use crate::compiler2::product_drive::drive_retained_root_backend_product;
    use crate::compiler2::pull::{ProductKey, ProductRequestId, ProductSessions, PullOutcome};
    use crate::compiler2::{FactKey, Job};
    use std::cell::RefCell;
    use std::collections::HashSet;

    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let evaluations = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&evaluations);
    tel.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
        &["fz", "compiler2", "pull", "product", "evaluated"],
        move |_, _, _, key, _, _| {
            if matches!(key, ProductKey::StructSchema(_)) {
                observed.borrow_mut().push(key.clone());
            }
        },
    );
    let mut world = World::new();
    world.submit_code(
        Some("published_schema.fz".to_string()),
        concat!(
            "defmodule Item do\n  defstruct [:value]\nend\n",
            "defmodule Other do\n  defstruct [:flag]\nend\n",
            "fn main() do\n  dbg(%Other{flag: 0})\n  %Item{value: 1}.value\nend\n",
        )
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let mut sessions = ProductSessions::default();
    let before = drive_retained_root_backend_product(&mut world, &tel, &mut sessions, root, None).unwrap();
    let item = world.reference_module("Item");
    let other = world.reference_module("Other");
    let item_key = ProductKey::StructSchema(item);
    let other_key = ProductKey::StructSchema(other);
    let item_generation = sessions.get(root).unwrap().memo().generation(&item_key).unwrap();
    let other_generation = sessions.get(root).unwrap().memo().generation(&other_key).unwrap();
    let item_allocations = schema_allocations(&before, "Item");
    let other_allocations = schema_allocations(&before, "Other");
    let fact = FactKey::StructDefined(item);
    let old_revision = world.fact_revision(&fact);
    evaluations.borrow_mut().clear();

    let mut definition = world.struct_def(item).unwrap().clone();
    definition.fields.push("added".to_string());
    assert!(world.define_struct_def(item, definition));
    let job = Job::DefineModule(item);
    let (outputs, reads) = world.standing_claims_and_reads(&job);
    ExecutionContext::with_product_sessions(&mut world, &tel, &mut sessions).complete_job(
        job,
        JobEffects {
            reads: reads.into_iter().collect(),
            outputs,
            changed: vec![fact.clone()],
            ..JobEffects::default()
        },
    );
    assert_ne!(world.fact_revision(&fact), old_revision);
    let schema_edited = drive_retained_root_backend_product(&mut world, &tel, &mut sessions, root, None).unwrap();
    let updated_item = schema_allocations(&schema_edited, "Item");
    let untouched_other = schema_allocations(&schema_edited, "Other");
    assert_eq!(updated_item.1.as_ref(), &["value".to_string(), "added".to_string()]);
    assert!(!Rc::ptr_eq(&item_allocations.1, &updated_item.1));
    assert!(Rc::ptr_eq(&other_allocations.0, &untouched_other.0));
    assert!(Rc::ptr_eq(&other_allocations.1, &untouched_other.1));
    assert_eq!(
        sessions.get(root).unwrap().memo().generation(&item_key),
        Some(item_generation + 1)
    );
    assert_eq!(
        sessions.get(root).unwrap().memo().generation(&other_key),
        Some(other_generation)
    );
    assert_eq!(
        evaluations.borrow().iter().cloned().collect::<HashSet<_>>(),
        HashSet::from([item_key])
    );
    assert_eq!(before.schema("Item").unwrap(), &["value".to_string()]);
    assert!(Rc::ptr_eq(&item_allocations.1, &schema_allocations(&before, "Item").1));
}
