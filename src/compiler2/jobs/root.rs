use std::collections::{HashMap, HashSet, VecDeque};

use super::super::drive::{FactKey, Job, JobEffects};
use super::super::identity::{ExecutableKey, RootId};
use super::super::scheduler::FatalError;
use super::super::semantic::SelectedCallee;
use super::super::world::World;
use crate::telemetry::opaque;
use crate::{measurements, metadata};

/// Seeds one semantic root once its entry definition exists.
///
/// A root entry is compiler-owned and can exist before the function does. The
/// seed publishes the root fact immediately, then waits until the entry
/// function is defined before it schedules the first closure walk.
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
    let Some(_function_revision) = world.function_defined_revision(root.function) else {
        effects.waits.push(function_fact);
        return Ok(effects);
    };

    effects.reads.push(function_fact);
    effects.follow_up.push(Job::LowerFunction(root.function));
    effects.follow_up.push(Job::PlanEntryDispatch(root.function));
    effects.follow_up.push(Job::CheckSemanticClosure(root_id));
    Ok(effects)
}

/// Walks one root's live semantic frontier and republishes its closure facts.
pub(super) fn check_semantic_closure(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let root = world.root_entry(root_id);
    let mut reads = vec![FactKey::RootEntry(root_id)];
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::new();
    let mut outputs = Vec::new();
    let mut revision = world.root_revision(root_id);

    let function_fact = FactKey::FunctionDefined(root.function);
    let Some(function_revision) = world.function_defined_revision(root.function) else {
        return Ok(JobEffects::wait_on(function_fact, []));
    };
    reads.push(function_fact);
    revision = revision.max(function_revision);

    let (entry_activation, entry_revision) = world.activate(root_id, root.function, Vec::new());
    let mut activation_revisions = HashMap::from([(entry_activation.clone(), entry_revision)]);
    let mut executable_needs = HashMap::from([(entry_activation.clone(), HashSet::from([root.need]))]);
    let mut queue = VecDeque::from([entry_activation]);
    let mut queued = HashSet::from([queue[0].clone()]);

    while let Some(activation) = queue.pop_front() {
        let activation_revision = *activation_revisions
            .get(&activation)
            .expect("queued activations should have a current revision");
        outputs.push((FactKey::Activation(activation.clone()), activation_revision));

        let analyzed_fact = FactKey::ActivationAnalyzed(activation.clone());
        let Some(analyzed_revision) = world.fact_revision(analyzed_fact.clone()) else {
            waits.insert(analyzed_fact);
            follow_up.insert(Job::AnalyzeActivation(activation.clone()));
            continue;
        };
        reads.push(analyzed_fact);
        revision = revision.max(analyzed_revision);

        let return_fact = FactKey::ReturnType(activation.clone());
        let Some(return_revision) = world.fact_revision(return_fact.clone()) else {
            waits.insert(return_fact);
            follow_up.insert(Job::AnalyzeActivation(activation.clone()));
            continue;
        };
        reads.push(return_fact);
        revision = revision.max(return_revision);

        let Some(analysis) = world.activation_analysis(&activation).cloned() else {
            waits.insert(FactKey::ActivationAnalyzed(activation.clone()));
            follow_up.insert(Job::AnalyzeActivation(activation.clone()));
            continue;
        };

        for callsite in &analysis.callsites {
            let key = super::super::semantic::CallSiteKey {
                activation: activation.clone(),
                callsite: *callsite,
            };
            let selected_fact = FactKey::SelectedCallee(key.clone());
            let Some(selected_revision) = world.fact_revision(selected_fact.clone()) else {
                waits.insert(selected_fact);
                follow_up.insert(Job::AnalyzeActivation(activation.clone()));
                continue;
            };
            reads.push(selected_fact);
            revision = revision.max(selected_revision);

            let return_need_fact = FactKey::ReturnNeed(key.clone());
            let Some(return_need_revision) = world.fact_revision(return_need_fact.clone()) else {
                waits.insert(return_need_fact);
                follow_up.insert(Job::AnalyzeActivation(activation.clone()));
                continue;
            };
            reads.push(return_need_fact);
            revision = revision.max(return_need_revision);

            let Some(summary) = world.callsite_summary(&key).cloned() else {
                waits.insert(FactKey::SelectedCallee(key));
                follow_up.insert(Job::AnalyzeActivation(activation.clone()));
                continue;
            };
            let SelectedCallee::Function(function) = summary.callee else {
                continue;
            };

            let (callee, callee_revision) = world.activate(root_id, function, summary.arg_types);
            let previous_revision = activation_revisions.insert(callee.clone(), callee_revision);
            let needs = executable_needs.entry(callee.clone()).or_default();
            let inserted_need = needs.insert(summary.need);
            let widened = previous_revision.is_some_and(|previous| previous != callee_revision);
            if queued.insert(callee.clone()) || widened || inserted_need {
                queue.push_back(callee);
            }
        }
    }

    let activations = activation_revisions.keys().cloned().collect::<Vec<_>>();
    let mut executables = Vec::new();
    for activation in &activations {
        let activation_revision = *activation_revisions
            .get(activation)
            .expect("frontier activations should have a current revision");
        for need in executable_needs
            .get(activation)
            .into_iter()
            .flat_map(|needs| needs.iter().copied())
        {
            let executable = ExecutableKey {
                activation: activation.clone(),
                need,
            };
            outputs.push((FactKey::Executable(executable.clone()), activation_revision));
            executables.push(executable);
        }
    }

    world.tel().execute(
        &["fz", "compiler2", "semantic_closed", "defined"],
        &measurements! {
            root_id: root_id.as_u32() as u64,
            revision: revision,
        },
        &metadata! {
            activations: opaque(&activations),
            executables: opaque(&executables),
        },
    );
    outputs.push((FactKey::SemanticClosed(root_id), revision));

    Ok(JobEffects {
        reads,
        waits: waits.into_iter().collect(),
        outputs: dedupe_outputs(outputs),
        follow_up: follow_up.into_iter().collect(),
    })
}

fn dedupe_outputs(outputs: Vec<(FactKey, u64)>) -> Vec<(FactKey, u64)> {
    let mut deduped: HashMap<FactKey, u64> = HashMap::new();
    for (fact, revision) in outputs {
        deduped
            .entry(fact)
            .and_modify(|current| *current = (*current).max(revision))
            .or_insert(revision);
    }
    deduped.into_iter().collect()
}
