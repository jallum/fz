use super::super::drive::{FactKey, Job, JobEffects};
use super::super::identity::{ExecutableKey, RootId};
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
    let (activation, activation_revision) = world.activate(root_id, root.function, Vec::new());
    let revision = root_revision.max(function_revision).max(activation_revision);
    let executable = ExecutableKey {
        activation: activation.clone(),
        need: root.need,
    };
    effects
        .outputs
        .push((FactKey::Activation(activation.clone()), activation_revision));
    effects.outputs.push((FactKey::Executable(executable), revision));
    effects.follow_up.push(Job::LowerFunction(root.function));
    effects.follow_up.push(Job::PlanEntryDispatch(root.function));
    effects.follow_up.push(Job::AnalyzeActivation(activation));
    effects.follow_up.push(Job::CheckSemanticClosure(root_id));
    Ok(effects)
}

/// Publishes the first semantic-closure marker for a seeded root.
///
/// This ticket keeps closure intentionally small: once the entry activation and
/// executable exist, the root can publish `SemanticClosed`. Later semantic jobs
/// will make this job stricter without changing the work-graph contract.
pub(super) fn check_semantic_closure(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let mut reads = vec![FactKey::RootEntry(root_id)];
    let mut revision = world.root_revision(root_id);
    for activation in world.root_activations(root_id) {
        let activation_fact = FactKey::Activation(activation.clone());
        let Some(activation_revision) = world.fact_revision(activation_fact.clone()) else {
            return Ok(JobEffects::wait_on(
                activation_fact,
                [Job::AnalyzeActivation(activation)],
            ));
        };
        reads.push(activation_fact);
        revision = revision.max(activation_revision);

        let analyzed_fact = FactKey::ActivationAnalyzed(activation.clone());
        let Some(analyzed_revision) = world.fact_revision(analyzed_fact.clone()) else {
            return Ok(JobEffects::wait_on(analyzed_fact, [Job::AnalyzeActivation(activation)]));
        };
        reads.push(analyzed_fact);
        revision = revision.max(analyzed_revision);

        let return_fact = FactKey::ReturnType(activation.clone());
        let Some(return_revision) = world.fact_revision(return_fact.clone()) else {
            return Ok(JobEffects::wait_on(return_fact, [Job::AnalyzeActivation(activation)]));
        };
        reads.push(return_fact);
        revision = revision.max(return_revision);
    }
    for executable in world.root_executables(root_id) {
        let executable_fact = FactKey::Executable(executable.clone());
        let Some(executable_revision) = world.fact_revision(executable_fact.clone()) else {
            return Ok(JobEffects::wait_on(executable_fact, []));
        };
        reads.push(executable_fact);
        revision = revision.max(executable_revision);
    }
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::SemanticClosed(root_id), revision)],
        ..JobEffects::default()
    })
}
