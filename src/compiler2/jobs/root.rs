use super::super::drive::{FactKey, Job, JobEffects};
use super::super::identity::{ActivationKey, ExecutableKey, RootId};
use super::super::scheduler::FatalError;
use super::super::world::World;

/// Seeds one semantic root once its entry definition exists.
///
/// A root entry is compiler-owned and can exist before the function does. The
/// seed publishes the root fact immediately, then waits until the entry
/// function is defined before it publishes the first activation and executable.
pub(super) fn seed_root(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let root = world.root_entry(root_id);
    let root_fact = FactKey::RootEntry(root_id);
    let root_revision = world.root_revision(root_id);
    let mut effects = JobEffects {
        reads: vec![root_fact.clone()],
        outputs: vec![(root_fact, root_revision)],
        ..JobEffects::default()
    };

    let function_fact = FactKey::FunctionDefined(root.function);
    let Some(function_revision) = world.function_defined_revision(root.function) else {
        effects.waits.push(function_fact);
        return Ok(effects);
    };

    effects.reads.push(function_fact);
    let revision = root_revision.max(function_revision);
    let activation = ActivationKey {
        root: root_id,
        function: root.function,
    };
    let executable = ExecutableKey {
        activation,
        need: root.need,
    };
    effects.outputs.push((FactKey::Activation(activation), revision));
    effects.outputs.push((FactKey::Executable(executable), revision));
    effects.follow_up.push(Job::LowerFunction(root.function));
    effects.follow_up.push(Job::CheckSemanticClosure(root_id));
    Ok(effects)
}

/// Publishes the first semantic-closure marker for a seeded root.
///
/// This ticket keeps closure intentionally small: once the entry activation and
/// executable exist, the root can publish `SemanticClosed`. Later semantic jobs
/// will make this job stricter without changing the work-graph contract.
pub(super) fn check_semantic_closure(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let root = world.root_entry(root_id);
    let activation = ActivationKey {
        root: root_id,
        function: root.function,
    };
    let executable = ExecutableKey {
        activation,
        need: root.need,
    };
    let mut reads = vec![FactKey::RootEntry(root_id)];
    let Some(activation_revision) = world.fact_revision(FactKey::Activation(activation)) else {
        return Ok(JobEffects::wait_on(FactKey::Activation(activation), []));
    };
    reads.push(FactKey::Activation(activation));
    let Some(executable_revision) = world.fact_revision(FactKey::Executable(executable)) else {
        return Ok(JobEffects::wait_on(FactKey::Executable(executable), []));
    };
    reads.push(FactKey::Executable(executable));
    let Some(lowered_revision) = world.fact_revision(FactKey::LoweredBody(root.function)) else {
        return Ok(JobEffects::wait_on(
            FactKey::LoweredBody(root.function),
            [Job::LowerFunction(root.function)],
        ));
    };
    reads.push(FactKey::LoweredBody(root.function));
    let revision = world
        .root_revision(root_id)
        .max(activation_revision)
        .max(executable_revision)
        .max(lowered_revision);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::SemanticClosed(root_id), revision)],
        ..JobEffects::default()
    })
}
