use super::super::drive::{FactKey, Job, JobEffects, current_uses, settled_uses};
use super::super::identity::{ExecutableKey, ExecutableNeed};
use super::super::scheduler::FatalError;
use super::super::semantic::CallableConstructionTargetKey;
use super::super::world::World;

pub(super) fn derive(world: &mut World, key: &CallableConstructionTargetKey) -> Result<JobEffects, FatalError> {
    let owner_fact = FactKey::ExecutableFacts(key.owner.clone());
    if !world.fact_is_settled(&owner_fact) {
        let job = Job::DeriveCallableConstructionTarget(key.clone());
        if world.work_graph.has_run(&job) && !world.has_fact(&owner_fact) {
            return Ok(JobEffects::default());
        }
        return Ok(JobEffects {
            waits: settled_uses([owner_fact]),
            ..JobEffects::default()
        });
    }

    let facts = world
        .executable_facts(&key.owner)
        .expect("settled executable facts should have a value");
    let Some(producer) = facts.callable_origin(key.value).cloned() else {
        return Ok(JobEffects {
            reads: current_uses([owner_fact]),
            ..JobEffects::default()
        });
    };
    let prerequisites = [
        owner_fact,
        FactKey::Recursive(producer.function),
        FactKey::InputDemand(producer.function),
    ];
    let waits = prerequisites
        .iter()
        .filter(|fact| !world.fact_is_settled(fact))
        .cloned()
        .collect::<Vec<_>>();
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(prerequisites.iter().filter(|fact| world.fact_is_settled(fact)).cloned()),
            waits: settled_uses(waits),
            ..JobEffects::default()
        });
    }

    let facts = world
        .executable_facts(&key.owner)
        .expect("settled executable facts should have a value");
    let Some(capture_types) = producer
        .captures
        .iter()
        .map(|capture| facts.analysis().value_types.get(capture).copied())
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(JobEffects {
            reads: current_uses(prerequisites),
            ..JobEffects::default()
        });
    };
    let mut inputs = capture_types;
    inputs.extend(key.surface.inputs.iter().copied());
    let target = ExecutableKey {
        activation: world.activation_key(key.owner.activation.root, producer.function, &inputs),
        need: ExecutableNeed::Value,
    };
    let fact = FactKey::CallableConstructionTarget(key.clone());
    let changed = world.define_callable_construction_target(key.clone(), target);
    Ok(JobEffects {
        reads: current_uses(prerequisites),
        outputs: vec![fact.clone()],
        changed: changed.then_some(fact).into_iter().collect(),
        ..JobEffects::default()
    })
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;
    use std::collections::HashSet;
    use std::rc::Rc;

    use super::super::super::ExecutableNeed;
    use super::super::super::JobCompletion;
    use super::super::super::drive::ExecutionContext;
    use super::super::super::facts::FactUse;
    use super::super::super::scheduler::DriveOutcome;
    use crate::telemetry::ConfiguredTelemetry;

    use super::*;

    #[test]
    fn construction_target_is_exact_memoized_and_read_without_formula_minting() {
        let tel = ConfiguredTelemetry::new();
        let observed = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&observed);
        tel.attach_raw_event2::<World, JobCompletion, _>(
            &["fz", "compiler2", "work_graph", "applied"],
            move |_, _, _, _, completion| {
                if let Job::DeriveCallableConstructionTarget(key) = &completion.job {
                    sink.borrow_mut().push(key.clone());
                }
            },
        );
        let mut world = World::new();
        world.submit_code(
            Some("construction_target_exact.fz".to_string()),
            "fn main() do\n  tag = 1\n  pair = fn (x) -> {tag, x} end\n  {pair.(1), pair}\nend\n".to_string(),
        );
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        world.demand(Job::BuildBackendProduct(root));
        assert!(matches!(
            ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Resolved
        ));

        let keys = observed.borrow().iter().cloned().collect::<HashSet<_>>();
        let key = keys
            .iter()
            .find(|key| key.surface.inputs.len() == 1 && world.types().is_integer(&key.surface.inputs[0]))
            .expect("the grounded integer surface should request one exact construction target")
            .clone();
        let fact = FactKey::CallableConstructionTarget(key.clone());
        let job = Job::DeriveCallableConstructionTarget(key.clone());
        let target = world
            .callable_construction_target(&key)
            .expect("the exact construction target should be published")
            .clone();
        let target_inputs = target.activation.inputs(world.types());
        assert_eq!(target_inputs.len(), key.surface.inputs.len() + 1);
        assert_eq!(
            &target_inputs[1..],
            key.surface.inputs.as_slice(),
            "the exact key surface must remain the target frame suffix after its complete capture vector",
        );
        assert_eq!(
            world.job_reads(&job),
            HashSet::from([
                FactUse::current(FactKey::ExecutableFacts(key.owner.clone())),
                FactUse::current(FactKey::Recursive(target.activation.function)),
                FactUse::current(FactKey::InputDemand(target.activation.function)),
            ]),
        );
        assert!(
            world
                .job_reads(&Job::DeriveRuntimeDemand(key.owner.clone()))
                .contains(&FactUse::current(fact.clone())),
            "RuntimeDemand should subscribe to the exact target fact it demanded",
        );

        let revision = world.fact_revision(&fact);
        let identities = world.types().identity_inventory();
        let effects = derive(&mut world, &key).expect("equal target derivation");
        assert_eq!(world.types().identity_inventory(), identities);
        let completion = world.complete_job(job, effects);
        assert!(completion.changed.is_empty());
        assert!(completion.wakes.is_empty());
        assert_eq!(world.fact_revision(&fact), revision);

        let owner_facts = Rc::clone(
            world
                .executable_facts(&key.owner)
                .expect("the original owner facts should still be published"),
        );
        world.submit_code(
            Some("construction_target_removal.fz".to_string()),
            "fn main(), do: 0\n".to_string(),
        );
        world.demand(Job::BuildBackendProduct(root));
        assert!(matches!(
            ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Resolved
        ));
        assert!(world.callable_construction_target(&key).is_none());
        assert!(world.fact_revision(&fact).is_none());
        assert!(
            world
                .job_outputs(&Job::DeriveCallableConstructionTarget(key.clone()))
                .is_empty()
        );

        assert!(world.define_executable_facts(key.owner.clone(), owner_facts));
        let owner_fact = FactKey::ExecutableFacts(key.owner.clone());
        world.complete_job(
            Job::DeriveExecutableFacts(key.owner.clone()),
            JobEffects {
                outputs: vec![owner_fact.clone()],
                changed: vec![owner_fact],
                ..JobEffects::default()
            },
        );
        world.demand(Job::DeriveRuntimeDemand(key.owner.clone()));
        assert!(matches!(
            ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Resolved
        ));
        assert_eq!(world.callable_construction_target(&key), Some(&target));
        assert!(world.fact_revision(&fact).is_some());
        assert!(
            world
                .job_outputs(&Job::DeriveCallableConstructionTarget(key.clone()))
                .contains(&fact),
            "the reappeared owner demand must republish the exact construction target",
        );
    }

    #[test]
    fn owner_fact_redefinition_replaces_the_target_through_its_producer() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        world.submit_code(
            Some("construction_target_replacement.fz".to_string()),
            "fn main() do\n  tag = 1\n  pair = fn (x) -> {tag, x} end\n  {pair.(1), pair}\nend\n".to_string(),
        );
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        world.demand(Job::BuildBackendProduct(root));
        assert!(matches!(
            ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Resolved
        ));

        let keys = world
            .runtime_demand_facts()
            .flat_map(|(owner, demand)| {
                demand.callable_flows.iter().flat_map(move |(&value, flow)| {
                    flow.first_class_surfaces
                        .iter()
                        .map(move |surface| CallableConstructionTargetKey {
                            owner: owner.clone(),
                            value,
                            surface: surface.clone(),
                        })
                })
            })
            .collect::<Vec<_>>();
        let key = keys
            .into_iter()
            .find(|key| key.surface.inputs.len() == 1 && world.types().is_integer(&key.surface.inputs[0]))
            .expect("the grounded first-class surface should have an exact target");
        let original = world
            .callable_construction_target(&key)
            .expect("the grounded first-class surface should have a published target")
            .clone();
        let target_fact = FactKey::CallableConstructionTarget(key.clone());
        let revision = world.fact_revision(&target_fact);
        let owner_facts = world
            .executable_facts(&key.owner)
            .expect("target owner facts")
            .as_ref()
            .clone();
        let producer = owner_facts
            .callable_origin(key.value)
            .expect("target owner callable producer")
            .clone();
        let mut replacement_facts = owner_facts;
        let atom = world.types_mut().atom();
        replacement_facts
            .analysis
            .value_types
            .insert(producer.captures[0], atom);
        assert!(world.define_executable_facts(key.owner.clone(), Rc::new(replacement_facts)));
        let owner_fact = FactKey::ExecutableFacts(key.owner.clone());
        world.complete_job(
            Job::DeriveExecutableFacts(key.owner.clone()),
            JobEffects {
                outputs: vec![owner_fact.clone()],
                changed: vec![owner_fact],
                ..JobEffects::default()
            },
        );
        assert!(matches!(
            ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Resolved
        ));

        let replacement = world
            .callable_construction_target(&key)
            .expect("the target producer should observe the replaced owner facts");
        assert_ne!(replacement, &original);
        assert!(world.fact_revision(&target_fact) > revision);
        assert_eq!(
            &replacement.activation.inputs(world.types())[1..],
            key.surface.inputs.as_slice(),
        );
    }

    #[test]
    fn late_independent_surface_waits_for_only_its_exact_construction_prerequisites() {
        let mut missing = World::new();
        let missing_root = missing.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let missing_function = missing.root_function(missing_root);
        let missing_owner = ExecutableKey {
            activation: super::super::super::ActivationKey::from_inputs(
                missing_root,
                missing_function,
                &[],
                missing.types_mut(),
            ),
            need: ExecutableNeed::Value,
        };
        let int = missing.types_mut().int();
        let missing_key = CallableConstructionTargetKey {
            owner: missing_owner.clone(),
            value: super::super::super::ValueId::from_u32(0),
            surface: super::super::super::semantic::CallableSurface::new(vec![int], missing.types_mut()),
        };
        let blocked = derive(&mut missing, &missing_key).expect("an absent owner should block the exact target");
        assert!(blocked.reads.is_empty());
        assert_eq!(
            blocked.waits,
            vec![FactUse::settled(FactKey::ExecutableFacts(missing_owner))],
        );
        assert!(blocked.outputs.is_empty());

        let tel = ConfiguredTelemetry::new();
        let observed = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&observed);
        tel.attach_raw_event2::<World, JobCompletion, _>(
            &["fz", "compiler2", "work_graph", "applied"],
            move |_, _, _, _, completion| {
                if let Job::DeriveCallableConstructionTarget(key) = &completion.job {
                    sink.borrow_mut().push(key.clone());
                }
            },
        );
        let mut world = World::new();
        world.submit_code(
            Some("construction_target_late_surface.fz".to_string()),
            "fn main() do\n  tag = 1\n  pair = fn (x) -> {tag, x} end\n  {pair.(1), pair}\nend\n".to_string(),
        );
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        world.demand(Job::BuildBackendProduct(root));
        assert!(matches!(
            ExecutionContext::new(&mut world, &tel).drive(),
            DriveOutcome::Resolved
        ));

        let existing = observed
            .borrow()
            .iter()
            .find(|key| key.surface.inputs.len() == 1)
            .expect("the first-class pair should demand its grounded integer surface")
            .clone();
        let function = world
            .executable_facts(&existing.owner)
            .and_then(|facts| facts.callable_origin(existing.value))
            .expect("the exact owner value should retain its callable producer")
            .function;
        let atom = world.types_mut().atom();
        let late_surface = super::super::super::semantic::CallableSurface::new(vec![atom], world.types_mut());
        let late = CallableConstructionTargetKey {
            owner: existing.owner.clone(),
            value: existing.value,
            surface: late_surface.clone(),
        };
        assert!(world.callable_construction_target(&late).is_none());

        assert!(world.fact_is_settled(&FactKey::Recursive(function)));
        assert!(world.fact_is_settled(&FactKey::InputDemand(function)));
        let owner_fact = FactKey::ExecutableFacts(late.owner.clone());
        let recursive_fact = FactKey::Recursive(function);
        let input_fact = FactKey::InputDemand(function);

        world.complete_job(Job::DeriveCallGraphComponent(function), JobEffects::default());
        if !world.fact_is_settled(&input_fact) {
            world.complete_job(
                Job::DeriveInputDemand(function),
                JobEffects {
                    outputs: vec![input_fact.clone()],
                    ..JobEffects::default()
                },
            );
        }
        world.complete_job(
            Job::DeriveExecutableFacts(late.owner.clone()),
            JobEffects {
                outputs: vec![owner_fact.clone()],
                ..JobEffects::default()
            },
        );
        assert!(world.fact_is_settled(&owner_fact));
        let missing_recursive = derive(&mut world, &late).expect("missing Recursive wait");
        assert_eq!(
            missing_recursive.reads,
            current_uses([owner_fact.clone(), input_fact.clone()])
        );
        assert_eq!(missing_recursive.waits, settled_uses([recursive_fact.clone()]));
        assert!(missing_recursive.outputs.is_empty());

        world.complete_job(
            Job::DeriveCallGraphComponent(function),
            JobEffects {
                outputs: vec![FactKey::CallGraphComponent(function), recursive_fact.clone()],
                ..JobEffects::default()
            },
        );
        world.complete_job(Job::DeriveInputDemand(function), JobEffects::default());
        world.complete_job(
            Job::DeriveExecutableFacts(late.owner.clone()),
            JobEffects {
                outputs: vec![owner_fact.clone()],
                ..JobEffects::default()
            },
        );
        assert!(world.fact_is_settled(&owner_fact));
        let missing_input = derive(&mut world, &late).expect("missing InputDemand wait");
        assert_eq!(missing_input.reads, current_uses([owner_fact, recursive_fact]));
        assert_eq!(missing_input.waits, settled_uses([input_fact.clone()]));
        assert!(missing_input.outputs.is_empty());

        world.complete_job(
            Job::DeriveInputDemand(function),
            JobEffects {
                outputs: vec![input_fact],
                ..JobEffects::default()
            },
        );
        let job = Job::DeriveCallableConstructionTarget(late.clone());
        let effects = derive(&mut world, &late).expect("restored prerequisites should publish the late target");
        assert_eq!(effects.outputs, vec![FactKey::CallableConstructionTarget(late.clone())]);
        world.complete_job(job, effects);
        let target = world
            .callable_construction_target(&late)
            .expect("the late surface should have its own exact target");
        let inputs = target.activation.inputs(world.types());
        assert_eq!(&inputs[inputs.len() - late_surface.inputs.len()..], late_surface.inputs);
        assert!(
            world.callable_construction_target(&existing).is_some(),
            "adding an independent surface must not retract the existing target",
        );
    }
}
