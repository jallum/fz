use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactUse;
use super::super::identity::{ActivationKey, ExecutableNeed, FunctionId, RootId};
use super::super::world::World;
use super::*;
use std::collections::HashMap;

fn executable(world: &mut World, id: u32) -> ExecutableKey {
    ExecutableKey {
        activation: ActivationKey::from_inputs(
            RootId::for_test(1),
            FunctionId::from_coordinate(id),
            &[],
            world.types_mut(),
        ),
        need: ExecutableNeed::Value,
    }
}

fn contribution(world: &World, slot: &InputSlot, source: IncomingInputSource) -> JobEffects {
    JobEffects {
        incoming_input_contributions: HashMap::from([(
            slot.clone(),
            IncomingInputSources::new(HashSet::from([source]), world.types()),
        )]),
        ..Default::default()
    }
}

#[test]
fn slot_ownership_extends_while_waiting_and_withdraws_only_the_concluding_publisher() {
    let mut world = World::new();
    let first = executable(&mut world, 1);
    let second = executable(&mut world, 2);
    let callee = executable(&mut world, 3);
    let slot = InputSlot {
        executable: callee.clone(),
        semantic_index: 0,
    };
    let fact = FactKey::IncomingInputSlot(slot.clone());
    let empty_owner = Job::DeriveRuntimeDemand(callee);
    world.complete_job(
        empty_owner,
        JobEffects {
            incoming_input_contributions: HashMap::from([(slot.clone(), IncomingInputSources::default())]),
            ..Default::default()
        },
    );
    assert!(world.fact_is_settled(&fact), "an authoritative empty slot is readable");
    assert!(world.incoming_input_sources(&slot).unwrap().is_empty());
    let first_source = IncomingInputSource {
        producer: first.clone(),
        value: ValueId::from_u32(1),
        role: IncomingInputRole::CallArgument,
    };
    let second_source = IncomingInputSource {
        producer: second.clone(),
        value: ValueId::from_u32(2),
        role: IncomingInputRole::CallArgument,
    };
    let first_job = Job::DeriveRuntimeDemand(first);
    let second_job = Job::DeriveRuntimeDemand(second);
    world.complete_job(first_job.clone(), contribution(&world, &slot, first_source.clone()));
    world.complete_job(second_job.clone(), contribution(&world, &slot, second_source.clone()));
    let both = Rc::clone(world.incoming_input_sources(&slot).unwrap());
    assert_eq!(both.len(), 2);
    let revision = world.fact_revision(&fact);
    world.complete_job(first_job.clone(), contribution(&world, &slot, first_source));
    assert_eq!(world.fact_revision(&fact), revision);
    assert!(
        Rc::ptr_eq(world.incoming_input_sources(&slot).unwrap(), &both),
        "equal publication preserves the allocation"
    );

    world.complete_job(
        first_job.clone(),
        JobEffects {
            waits: vec![FactUse::current(FactKey::CodeScoped(
                super::super::SourceOwner::for_test(0),
            ))],
            ..Default::default()
        },
    );
    assert!(!world.fact_is_settled(&fact));
    assert!(
        Rc::ptr_eq(world.incoming_input_sources(&slot).unwrap(), &both),
        "a waiting publisher does not recant sources it has not reached"
    );
    world.complete_job(first_job, JobEffects::default());
    assert!(world.fact_is_settled(&fact));
    assert_eq!(world.incoming_input_sources(&slot).unwrap().as_ref(), &[second_source]);
    world.complete_job(second_job, JobEffects::default());
    assert!(world.fact_is_settled(&fact));
    assert!(
        world.incoming_input_sources(&slot).unwrap().is_empty(),
        "withdrawing the last edge preserves the target's empty answer"
    );
}
