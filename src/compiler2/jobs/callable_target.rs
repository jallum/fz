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
#[path = "callable_target_test.rs"]
mod callable_target_test;
