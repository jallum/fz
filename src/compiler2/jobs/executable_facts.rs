//! Scheduler producer for the World-owned `ExecutableFacts(E)` direct fact.

use super::super::drive::{FactKey, JobEffects, settled_uses};
use super::super::executable_facts::project_executable_facts;
use super::super::identity::ExecutableKey;
use super::super::scheduler::FatalError;
use super::super::semantic::CallSiteKey;
use super::super::world::World;

pub(super) fn derive_executable_facts(world: &mut World, executable: &ExecutableKey) -> Result<JobEffects, FatalError> {
    let activation = &executable.activation;
    let analyzed = FactKey::ActivationAnalyzed(activation.clone());
    if !world.fact_is_settled(&analyzed) {
        return Ok(JobEffects {
            waits: settled_uses([analyzed]),
            ..JobEffects::default()
        });
    }

    let analysis = world
        .activation_analysis(activation)
        .expect("settled activation analysis fact should have analysis")
        .clone();
    let mut prerequisites = vec![
        analyzed,
        FactKey::LoweredBody(activation.function),
        FactKey::EntryDispatch(activation.function),
    ];
    prerequisites.extend(analysis.callsites.iter().map(|callsite| {
        FactKey::CallSiteSummary(CallSiteKey {
            activation: activation.clone(),
            callsite: *callsite,
        })
    }));
    let waits = prerequisites
        .iter()
        .filter(|fact| !world.fact_is_settled(fact))
        .cloned()
        .collect::<Vec<_>>();
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: settled_uses([prerequisites[0].clone()]),
            waits: settled_uses(waits),
            ..JobEffects::default()
        });
    }

    let facts = project_executable_facts(world, executable, analysis);
    let fact = FactKey::ExecutableFacts(executable.clone());
    let changed = world.define_executable_facts(executable.clone(), facts);
    Ok(JobEffects {
        reads: settled_uses(prerequisites),
        outputs: vec![fact.clone()],
        changed: changed.then_some(fact).into_iter().collect(),
        ..JobEffects::default()
    })
}
