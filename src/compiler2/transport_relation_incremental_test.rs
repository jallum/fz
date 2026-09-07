//! Exact callable-input facts stay local across retained root requests.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::telemetry::ConfiguredTelemetry;

use super::facts::FactUse;
use super::incoming_inputs::{IncomingInputSource, InputSlot};
use super::pull::{ProductKey, ProductRequestId, PullOutcome, PullSession, PullSessionId, PullWait};
use super::transport::{ActivationSymbol, ExecutableSymbol, TransportPosition};
use super::{CodeSubmission, Compiler2, DependencyKey, ExecutableNeed, FactKey, Job, RootSubmission, World};

#[derive(Default)]
struct Relations {
    abis: HashMap<super::RootId, Vec<(super::ExecutableKey, Rc<super::artifact::AbiReadyExecutable>)>>,
    facts: HashMap<InputSlot, Rc<[IncomingInputSource]>>,
    changed: Vec<InputSlot>,
    content_moves: HashSet<FactKey>,
    evaluated: Vec<(super::RootId, ProductKey)>,
    requested: Vec<(super::RootId, ProductKey)>,
    cached: Vec<(super::RootId, ProductKey)>,
    displaced: Vec<(super::RootId, ProductKey)>,
    waited: Vec<(super::RootId, ProductKey, Vec<PullWait>)>,
    reads: HashMap<(super::RootId, ProductKey), Vec<FactUse<FactKey>>>,
    pending: Vec<Vec<ProductEvent>>,
}

enum ProductEvent {
    Requested(ProductKey),
    Cached(ProductKey),
    Evaluated(ProductKey),
    Waiting(ProductKey, Vec<PullWait>),
    Displaced(ProductKey),
}

impl Relations {
    fn assert_reader_work(&self, root: super::RootId, reader: &ProductKey, slot: &InputSlot, expected: (usize, usize)) {
        let address = (root, reader.clone());
        let counts = (
            self.evaluated.iter().filter(|event| *event == &address).count(),
            self.displaced.iter().filter(|event| *event == &address).count(),
        );
        let waits = self
            .waited
            .iter()
            .filter(|(owner, key, _)| *owner == root && key == reader)
            .collect::<Vec<_>>();
        assert_eq!(
            counts, expected,
            "exact input-owner evaluations/displacements; waits: {waits:?}"
        );
        assert!(
            waits.is_empty(),
            "the exact input-owner prerequisites must settle before production: {waits:?}"
        );
        if counts.0 != 0 {
            assert!(
                self.reads[&address].contains(&FactUse::settled(FactKey::IncomingInputSlot(slot.clone()))),
                "the reevaluated owner directly consumes the exact moved slot"
            );
            let moved_reads = self.reads[&address]
                .iter()
                .filter(|usage| self.content_moves.contains(usage.fact()))
                .map(|usage| usage.fact().clone())
                .collect::<HashSet<_>>();
            let moved_slot = self
                .changed
                .contains(slot)
                .then(|| FactKey::IncomingInputSlot(slot.clone()))
                .into_iter()
                .collect::<HashSet<_>>();
            assert_eq!(
                moved_reads, moved_slot,
                "only the exact input-slot content moved among this owner's direct fact reads"
            );
        }
    }
}

fn observe(telemetry: &ConfiguredTelemetry) -> Rc<RefCell<Relations>> {
    let relations = Rc::new(RefCell::new(Relations::default()));
    let observed = Rc::clone(&relations);
    telemetry.attach_raw_event2::<World, super::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, world, completion| {
            for change in &completion.changed {
                if let DependencyKey::Fact(fact) = &change.key
                    && change.old_revision != change.new_revision
                {
                    observed.borrow_mut().content_moves.insert(fact.clone());
                }
                if let DependencyKey::Fact(FactKey::IncomingInputSlot(slot)) = &change.key {
                    if change.old_revision != change.new_revision {
                        observed.borrow_mut().changed.push(slot.clone());
                    }
                    if let Some(sources) = world.incoming_input_sources(slot) {
                        observed.borrow_mut().facts.insert(slot.clone(), Rc::clone(sources));
                    }
                }
            }
        },
    );
    let observed = Rc::clone(&relations);
    telemetry.attach_raw_event1::<PullSessionId, _>(
        &["fz", "compiler2", "pull", "session", "started"],
        move |_, _, _, _| observed.borrow_mut().pending.push(Vec::new()),
    );
    let observed = Rc::clone(&relations);
    telemetry.attach_raw_event1::<PullSession, _>(
        &["fz", "compiler2", "pull", "session", "finished"],
        move |_, _, _, session| {
            let mut observed = observed.borrow_mut();
            observed.abis.insert(
                session.root(),
                session
                    .memo()
                    .abi_executables()
                    .map(|(key, abi)| (key.clone(), Rc::clone(abi)))
                    .collect(),
            );
            let events = observed.pending.pop().expect("balanced retained activation");
            for event in events {
                match event {
                    ProductEvent::Requested(key) => observed.requested.push((session.root(), key)),
                    ProductEvent::Cached(key) => observed.cached.push((session.root(), key)),
                    ProductEvent::Evaluated(key) => {
                        if matches!(
                            &key,
                            ProductKey::CallableConstruction(TransportPosition::ExecutableInput { .. })
                        ) {
                            observed.reads.insert(
                                (session.root(), key.clone()),
                                session
                                    .memo()
                                    .fact_dependencies(&key)
                                    .expect("retained callable-input owner")
                                    .keys()
                                    .cloned()
                                    .collect(),
                            );
                        }
                        observed.evaluated.push((session.root(), key));
                    }
                    ProductEvent::Waiting(key, waits) => observed.waited.push((session.root(), key, waits)),
                    ProductEvent::Displaced(key) => observed.displaced.push((session.root(), key)),
                }
            }
        },
    );
    let observed = Rc::clone(&relations);
    telemetry.attach_raw_event2::<ProductKey, ProductRequestId, _>(
        &["fz", "compiler2", "pull", "product", "requested"],
        move |_, _, _, key, _| {
            observed
                .borrow_mut()
                .pending
                .last_mut()
                .expect("active request session")
                .push(ProductEvent::Requested(key.clone()))
        },
    );
    let observed = Rc::clone(&relations);
    telemetry.attach_raw_event1::<ProductKey, _>(
        &["fz", "compiler2", "pull", "product", "cache_hit"],
        move |_, _, _, key| {
            observed
                .borrow_mut()
                .pending
                .last_mut()
                .expect("active cache-hit session")
                .push(ProductEvent::Cached(key.clone()))
        },
    );
    let observed = Rc::clone(&relations);
    telemetry.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
        &["fz", "compiler2", "pull", "product", "evaluated"],
        move |_, _, _, key, _, outcome| {
            let mut observed = observed.borrow_mut();
            let events = observed.pending.last_mut().expect("active product session");
            events.push(ProductEvent::Evaluated(key.clone()));
            if let PullOutcome::Waiting(waits) = outcome {
                events.push(ProductEvent::Waiting(key.clone(), waits.clone()));
            }
        },
    );
    let observed = Rc::clone(&relations);
    telemetry.attach_raw_event1::<ProductKey, _>(
        &["fz", "compiler2", "pull", "product", "displaced"],
        move |_, _, _, key| {
            observed
                .borrow_mut()
                .pending
                .last_mut()
                .expect("active displacement session")
                .push(ProductEvent::Displaced(key.clone()))
        },
    );
    relations
}

fn root(compiler: &mut Compiler2<ConfiguredTelemetry>, name: &str) -> super::RootId {
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: name.into(),
        arity: 0,
        need: ExecutableNeed::Value,
    })
}

fn apply_slot(compiler: &mut Compiler2<ConfiguredTelemetry>, relations: &Relations, root: super::RootId) -> InputSlot {
    let helpers = compiler.world_mut().reference_module("Helpers");
    let apply = compiler.world_mut().reference_function(helpers, "apply", 1);
    let slots = relations
        .facts
        .keys()
        .filter(|slot| {
            slot.executable.activation.root == root
                && slot.executable.activation.function == apply
                && slot.semantic_index == 0
        })
        .cloned()
        .collect::<Vec<_>>();
    assert_eq!(slots.len(), 1, "the fixture has one typed apply/1 input per root");
    slots[0].clone()
}

fn owner(world: &World, slot: &InputSlot) -> ProductKey {
    ProductKey::CallableConstruction(TransportPosition::ExecutableInput {
        executable: ExecutableSymbol {
            activation: ActivationSymbol {
                function: slot.executable.activation.function,
                arrow: slot.executable.activation.arrow,
                input: slot.executable.activation.inputs(world.types()).into_boxed_slice(),
            },
            need: slot.executable.need,
        },
        semantic_index: slot.semantic_index,
    })
}

#[test]
fn generic_callable_owner_appears_and_withdraws_with_its_positioned_obligation() {
    let telemetry = ConfiguredTelemetry::new();
    let relations = observe(&telemetry);
    let output = crate::exec::runtime::DbgCapture::new();
    let mut compiler = Compiler2::new(telemetry);
    compiler.set_output(output.sink());
    compiler.submit_code(CodeSubmission {
        name: Some("generic_owner_transition.fz".into()),
        text: "fn value(), do: 42\nfn main() do\n  dbg(value())\n  0\nend\n".into(),
    });
    let root = root(&mut compiler, "main");
    assert_eq!(compiler.run_root_interp(root), Ok(0));
    let (main, abi) = relations.borrow().abis[&root]
        .iter()
        .find(|(key, _)| compiler.world().function_ref(key.activation.function).name == "main")
        .map(|(key, abi)| (key.clone(), Rc::clone(abi)))
        .unwrap();
    let super::body::LoweredBody::Clauses { entries, .. } = &abi.materialized.body else {
        unreachable!()
    };
    let value = entries
        .iter()
        .find_map(|entry| match &entry.tail {
            super::body::LoweredTail::DirectCall { value, callee, .. }
                if compiler.world().function_ref(*callee).name == "value" =>
            {
                Some(*value)
            }
            _ => None,
        })
        .expect("the source has one reached value call");
    let position = TransportPosition::Value {
        executable: abi.transport.executable.clone(),
        value,
    };
    let owner = ProductKey::CallableConstruction(position.clone());
    let shape = ProductKey::TransportShape(position.clone());
    assert!(!abi.callable_owners.iter().any(|owner| owner.position == position));
    assert!(!relations.borrow().requested.contains(&(root, owner.clone())));
    assert_eq!(compiler.retained_product_generation(root, &owner), None);
    let initial_shape_generation = compiler.retained_product_generation(root, &shape).unwrap();
    *relations.borrow_mut() = Relations::default();
    compiler.submit_code(CodeSubmission {
        name: Some("introduce_generic_callable.fz".into()),
        text: "fn value(), do: fn x -> x + 1 end\n".into(),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(0));
    let observed = relations.borrow();
    let abi = &observed.abis[&root].iter().find(|(key, _)| key == &main).unwrap().1;
    let demand = compiler.world().runtime_demand(&main).unwrap();
    assert!(demand.value_demands[&value].is_callable());
    assert!(
        !demand.callable_flows.contains_key(&value),
        "the call result is generic, not a local constructor"
    );
    let positioned = abi
        .callable_owners
        .iter()
        .find(|owner| owner.position == position)
        .expect("the exact call-result position gains a callable owner");
    assert!(positioned.owner.construction.is_none());
    assert!(!positioned.owner.callable_facts.is_empty());
    assert!(!positioned.owner.boundary_facts.is_empty());
    assert!(observed.evaluated.contains(&(root, owner.clone())));
    assert!(observed.evaluated.contains(&(root, shape.clone())));
    assert!(compiler.retained_product_generation(root, &shape).unwrap() > initial_shape_generation);
    drop(observed);
    *relations.borrow_mut() = Relations::default();
    compiler.submit_code(CodeSubmission {
        name: Some("withdraw_generic_callable.fz".into()),
        text: "fn value(), do: 42\n".into(),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(0));
    let observed = relations.borrow();
    let abi = &observed.abis[&root].iter().find(|(key, _)| key == &main).unwrap().1;
    assert!(!compiler.world().runtime_demand(&main).unwrap().value_demands[&value].is_callable());
    assert!(!abi.callable_owners.iter().any(|owner| owner.position == position));
    assert!(
        !observed.requested.contains(&(root, owner.clone())),
        "withdrawn owner has no downstream request"
    );
    assert!(
        !observed.evaluated.contains(&(root, owner)),
        "withdrawn callable obligation causes no producer work"
    );
    assert!(
        observed.evaluated.contains(&(root, shape)),
        "the physical scalar layout still belongs to its position"
    );
}

#[test]
fn retained_transport_obligations_follow_the_exact_input_demand_edit() {
    let telemetry = ConfiguredTelemetry::new();
    let relations = observe(&telemetry);
    let mut compiler = Compiler2::new(telemetry);
    compiler.submit_code(CodeSubmission {
        name: Some("retained_transport_obligations.fz".into()),
        text: "fn discard(_), do: 0\nfn forward(x), do: discard(x)\nfn inc(x), do: x + 1\nfn apply(fun), do: fun.(41)\nfn main(), do: forward(42) + apply(&inc/1)\n".into(),
    });
    let root = root(&mut compiler, "main");
    assert_eq!(compiler.run_root_interp(root), Ok(42));
    let forward = relations.borrow().abis[&root]
        .iter()
        .find(|(key, _)| compiler.world().function_ref(key.activation.function).name == "forward")
        .map(|(key, _)| key.clone())
        .unwrap();
    let slot = InputSlot {
        executable: forward.clone(),
        semantic_index: 0,
    };
    let ProductKey::CallableConstruction(position) = owner(compiler.world(), &slot) else {
        unreachable!()
    };
    let shape = ProductKey::TransportShape(position.clone());
    let construction = ProductKey::CallableConstruction(position.clone());
    let assert_absent = |compiler: &Compiler2<ConfiguredTelemetry>, observed: &Relations| {
        assert!(compiler.world().runtime_demand(&forward).unwrap().input_demands[0].is_ignore());
        let abi = observed.abis[&root].iter().find(|(key, _)| key == &forward).unwrap();
        assert!(!abi.1.transport.input_positions.contains(&position));
        assert!(!abi.1.callable_owners.iter().any(|owner| owner.position == position));
        assert!(
            !observed
                .requested
                .iter()
                .any(|(owner, key)| *owner == root && (key == &shape || key == &construction)),
            "ignored positioned products are never requested, not merely served from cache"
        );
        assert!(
            !observed
                .evaluated
                .iter()
                .any(|(owner, key)| *owner == root && (key == &shape || key == &construction)),
            "the ignored input has no exact positioned producer evaluations"
        );
    };
    assert_absent(&compiler, &relations.borrow());
    let retained = relations.borrow().abis[&root]
        .iter()
        .find(|(key, _)| compiler.world().function_ref(key.activation.function).name == "apply")
        .map(|(key, abi)| (key.clone(), Rc::clone(abi)))
        .unwrap();
    let retained_owner = retained
        .1
        .callable_owners
        .iter()
        .find(|positioned| matches!(positioned.position, TransportPosition::ExecutableInput { .. }))
        .unwrap()
        .clone();
    let retained_key = ProductKey::CallableConstruction(retained_owner.position.clone());
    let retained_generation = compiler.retained_product_generation(root, &retained_key).unwrap();
    let retained_shape = ProductKey::TransportShape(retained_owner.position.clone());
    let retained_shape_generation = compiler.retained_product_generation(root, &retained_shape).unwrap();
    for edit in [None, Some("fn unrelated(), do: 99\n")] {
        *relations.borrow_mut() = Relations::default();
        if let Some(text) = edit {
            compiler.submit_code(CodeSubmission {
                name: Some("unrelated_transport_edit.fz".into()),
                text: text.into(),
            });
        }
        assert_eq!(compiler.run_root_interp(root), Ok(42));
        assert!(
            relations.borrow().evaluated.is_empty(),
            "unchanged or unrelated request evaluates no product"
        );
        assert_absent(&compiler, &relations.borrow());
        assert_eq!(
            relations.borrow().cached,
            vec![(root, ProductKey::RootBackendProduct(root))]
        );
    }
    *relations.borrow_mut() = Relations::default();
    compiler.submit_code(CodeSubmission {
        name: Some("reached_transport_edit.fz".into()),
        text: "fn discard(x), do: x\n".into(),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(84));
    assert!(!compiler.world().runtime_demand(&forward).unwrap().input_demands[0].is_ignore());
    assert!(
        relations.borrow().evaluated.contains(&(root, shape.clone())),
        "changed input demand creates its exact shape consumer"
    );
    assert!(
        !relations.borrow().evaluated.contains(&(root, construction.clone())),
        "scalar input still has no callable owner"
    );
    let observed = relations.borrow();
    let abi = &observed.abis[&root].iter().find(|(key, _)| key == &forward).unwrap().1;
    assert!(abi.transport.input_positions.contains(&position));
    let unaffected = &observed.abis[&root]
        .iter()
        .find(|(key, _)| key == &retained.0)
        .unwrap()
        .1;
    let unaffected_owner = unaffected
        .callable_owners
        .iter()
        .find(|positioned| positioned.position == retained_owner.position)
        .unwrap();
    assert!(
        Rc::ptr_eq(&retained_owner.owner, &unaffected_owner.owner),
        "the independent callable owner keeps its allocation"
    );
    assert_eq!(
        compiler.retained_product_generation(root, &retained_key),
        Some(retained_generation)
    );
    assert_eq!(
        compiler.retained_product_generation(root, &retained_shape),
        Some(retained_shape_generation)
    );
    assert!(
        !observed.evaluated.contains(&(root, retained_shape)),
        "the independent positioned shape does no work"
    );
    assert!(
        !observed.evaluated.contains(&(root, retained_key)),
        "the independent callable obligation does no work"
    );
    drop(observed);
    *relations.borrow_mut() = Relations::default();
    compiler.submit_code(CodeSubmission {
        name: Some("withdraw_transport_input.fz".into()),
        text: "fn discard(_), do: 0\n".into(),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(42));
    assert_absent(&compiler, &relations.borrow());
}

#[test]
fn retained_callable_input_relations_ignore_unchanged_and_unrelated_requests() {
    let telemetry = ConfiguredTelemetry::new();
    let relations = observe(&telemetry);
    let mut compiler = Compiler2::new(telemetry);
    compiler.submit_code(CodeSubmission {
        name: Some("retained_callable_relations.fz".into()),
        text: "defmodule Helpers do\nfn apply(fun), do: fun.(41)\nfn make_adder(a), do: fn x -> x + a end\nend\nfn main(), do: Helpers.apply(Helpers.make_adder(1))\nfn control(), do: Helpers.apply(Helpers.make_adder(2))\n".into(),
    });
    let main = root(&mut compiler, "main");
    let control = root(&mut compiler, "control");
    assert_eq!(compiler.run_root_interp(main), Ok(42));
    assert_eq!(compiler.run_root_interp(control), Ok(43));
    let slot = apply_slot(&mut compiler, &relations.borrow(), main);
    let control_slot = apply_slot(&mut compiler, &relations.borrow(), control);
    let control_owner = owner(compiler.world(), &control_slot);
    let main_owner = owner(compiler.world(), &slot);
    let main_generation = compiler.retained_product_generation(main, &main_owner).unwrap();
    let control_generation = compiler.retained_product_generation(control, &control_owner).unwrap();
    let local = Rc::clone(compiler.world().incoming_input_sources(&slot).unwrap());
    let control_local = Rc::clone(compiler.world().incoming_input_sources(&control_slot).unwrap());
    assert_eq!(local.len(), 1);
    assert!(local.iter().all(|source| source.producer.activation.root == main));
    assert!(
        control_local
            .iter()
            .all(|source| source.producer.activation.root == control)
    );
    let revision = compiler
        .world()
        .fact_revision(&FactKey::IncomingInputSlot(slot.clone()));
    *relations.borrow_mut() = Relations::default();
    assert_eq!(compiler.run_root_interp(main), Ok(42));
    assert_eq!(compiler.run_root_interp(control), Ok(43));
    assert!(relations.borrow().evaluated.is_empty());
    assert!(relations.borrow().changed.is_empty());
    compiler.submit_code(CodeSubmission {
        name: Some("unrelated_callable_relation_edit.fz".into()),
        text: "fn unrelated(), do: 99\n".into(),
    });
    assert_eq!(compiler.run_root_interp(main), Ok(42));
    assert_eq!(compiler.run_root_interp(control), Ok(43));
    assert!(
        relations.borrow().evaluated.is_empty(),
        "unrelated source cannot initiate product production"
    );
    assert!(relations.borrow().changed.is_empty());

    relations.borrow().assert_reader_work(main, &main_owner, &slot, (0, 0));
    relations
        .borrow()
        .assert_reader_work(control, &control_owner, &control_slot, (0, 0));

    let producer = Job::DeriveRuntimeDemand(local[0].producer.clone());
    let completion = compiler.reproduce_job_for_test(producer.clone(), vec![]);
    assert_eq!(completion.job, producer);
    assert!(
        completion
            .changed
            .iter()
            .all(|change| change.old_revision == change.new_revision)
    );
    assert!(
        completion.wakes.is_empty(),
        "equal contribution reproduction wakes no semantic reader"
    );
    assert_eq!(compiler.run_root_interp(main), Ok(42));
    assert_eq!(
        compiler
            .world()
            .fact_revision(&FactKey::IncomingInputSlot(slot.clone())),
        revision
    );
    assert!(Rc::ptr_eq(
        &local,
        compiler.world().incoming_input_sources(&slot).unwrap()
    ));
    assert!(
        relations.borrow().changed.is_empty(),
        "equal producer reproduction does not move relation content"
    );
    assert_eq!(
        compiler.retained_product_generation(main, &main_owner),
        Some(main_generation)
    );
    relations.borrow().assert_reader_work(main, &main_owner, &slot, (0, 0));
    assert!(!relations.borrow().evaluated.contains(&(control, control_owner.clone())));
    *relations.borrow_mut() = Relations::default();

    compiler.submit_code(CodeSubmission {
        name: Some("reached_callable_relation_edit.fz".into()),
        text: "alias Helpers\nfn main(), do: Helpers.apply(Helpers.make_adder(3))\n".into(),
    });
    assert_eq!(compiler.run_root_interp(main), Ok(44));
    assert!(
        relations.borrow().changed.is_empty(),
        "a changed value on the same typed caller edge does not change its relation"
    );
    assert!(Rc::ptr_eq(
        &local,
        compiler.world().incoming_input_sources(&slot).unwrap()
    ));
    assert_eq!(
        compiler.world().fact_revision(&FactKey::IncomingInputSlot(slot)),
        revision
    );
    assert!(!relations.borrow().evaluated.contains(&(control, control_owner.clone())));
    assert_eq!(
        compiler.retained_product_generation(control, &control_owner),
        Some(control_generation)
    );
    assert!(Rc::ptr_eq(
        &control_local,
        compiler.world().incoming_input_sources(&control_slot).unwrap()
    ));
    *relations.borrow_mut() = Relations::default();
    assert_eq!(compiler.run_root_interp(control), Ok(43));
    assert!(relations.borrow().evaluated.is_empty());
    assert!(relations.borrow().changed.is_empty());
    assert!(relations.borrow().pending.is_empty());
}

#[test]
fn adding_and_removing_a_caller_edge_updates_the_existing_input_slot() {
    let telemetry = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&telemetry, &["fz", "diag"]);
    let relations = observe(&telemetry);
    let mut compiler = Compiler2::new(telemetry);
    compiler.submit_code(CodeSubmission {
        name: Some("one_callable_edge.fz".into()),
        text: "defmodule Helpers do\nfn apply(fun), do: fun.(41)\nfn make_adder(a), do: fn x -> x + a end\nend\nfn main(), do: Helpers.apply(Helpers.make_adder(1))\n".into(),
    });
    let main = root(&mut compiler, "main");
    assert_eq!(compiler.run_root_interp(main), Ok(42));
    let slot = apply_slot(&mut compiler, &relations.borrow(), main);
    let key = FactKey::IncomingInputSlot(slot.clone());
    let reader = owner(compiler.world(), &slot);
    let revision = compiler.world().fact_revision(&key).unwrap();
    let first = Rc::clone(compiler.world().incoming_input_sources(&slot).unwrap());
    assert_eq!(first.len(), 1);
    let main_function = compiler.root_function(main);
    assert_eq!(first[0].producer.activation.function, main_function);
    for (source, result, count, expected_revision) in [
        (
            "alias Helpers\nfn main() do\n  a = Helpers.make_adder(1)\n  b = Helpers.make_adder(1)\n  Helpers.apply(a) + Helpers.apply(b)\nend\n",
            84,
            2,
            revision + 1,
        ),
        (
            "alias Helpers\nfn main(), do: Helpers.apply(Helpers.make_adder(1))\n",
            42,
            1,
            revision + 2,
        ),
    ] {
        *relations.borrow_mut() = Relations::default();
        compiler.submit_code(CodeSubmission {
            name: Some("changed_callable_edges.fz".into()),
            text: source.into(),
        });
        assert_eq!(compiler.run_root_interp(main), Ok(result), "{:?}", diagnostics.events());
        let sources = compiler.world().incoming_input_sources(&slot).unwrap();
        assert_eq!(
            sources.len(),
            count,
            "caller replacement owns exactly its current input edges"
        );
        assert!(
            sources
                .iter()
                .all(|source| source.producer.activation.function == main_function)
        );
        assert_eq!(compiler.world().fact_revision(&key), Some(expected_revision));
        relations.borrow().assert_reader_work(main, &reader, &slot, (1, 1));
        assert_eq!(
            relations
                .borrow()
                .changed
                .iter()
                .filter(|changed| *changed == &slot)
                .count(),
            1,
            "one caller edit changes the local relation exactly once"
        );
        if count == 1 {
            assert_eq!(
                sources.as_ref(),
                first.as_ref(),
                "removal restores the original exact source edge"
            );
        }
    }
}
