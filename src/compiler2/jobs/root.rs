use std::collections::HashSet;
use std::collections::VecDeque;

use super::super::drive::{FactKey, Job, JobEffects};
use super::super::identity::{ExecutableKey, RootId};
use super::super::scheduler::FatalError;
use super::super::semantic::{CallSiteKey, DependencySnapshot, SelectedCallee, SemanticClosure};
use super::super::world::World;
use super::semantic::executable_callsite_needs;

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
        let mut wait = world.wait_for_function_definition(root.function);
        effects.waits.append(&mut wait.waits);
        effects.follow_up.append(&mut wait.follow_up);
        return Ok(effects);
    };

    effects.reads.push(function_fact);
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::new();
    if !world.require_activation_key_facts(root.function, &mut effects.reads, &mut waits, &mut follow_up) {
        effects.waits.extend(waits);
        effects.follow_up.extend(follow_up);
        return Ok(effects);
    }

    let entry_activation = world.activation_key(root_id, root.function, &[]);
    // An activation fact is fully determined by its key (the canonical
    // inputs live there), so once present it never changes.
    effects.outputs.push((FactKey::Activation(entry_activation.clone()), 1));
    effects.outputs.push((
        FactKey::Executable(ExecutableKey {
            activation: entry_activation.clone(),
            need: root.need,
        }),
        1,
    ));
    effects.follow_up.push(Job::LowerFunction(root.function));
    effects.follow_up.push(Job::PlanEntryDispatch(root.function));
    effects.follow_up.push(Job::AnalyzeActivation(entry_activation));
    effects.follow_up.push(Job::SealSemanticClosure(root_id));
    Ok(effects)
}

/// Seals a root's semantic closure once its activation frontier has settled.
///
/// This reads the activation, analysis, and callsite facts that
/// `analyze_activation` publishes, derives executable-specific call edges from
/// the executable frontier itself, and seals `SemanticClosed` once that
/// frontier stops growing.
pub(super) fn seal_semantic_closure(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let root = world.root_entry(root_id);
    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut follow_up = HashSet::new();
    let mut outputs = Vec::new();
    let mut dependencies = DependencySnapshot::default();

    let root_fact = FactKey::RootEntry(root_id);
    if let Some(root_revision) = world.fact_revision(root_fact.clone()) {
        reads.push(root_fact.clone());
        dependencies.record(root_fact, root_revision);
    } else {
        waits.insert(root_fact);
        follow_up.insert(Job::SeedRoot(root_id));
    }

    let function_fact = FactKey::FunctionDefined(root.function);
    let function_ready = if let Some(function_revision) = world.function_defined_revision(root.function) {
        reads.push(function_fact.clone());
        dependencies.record(function_fact, function_revision);
        true
    } else {
        let wait = world.wait_for_function_definition(root.function);
        waits.extend(wait.waits);
        follow_up.extend(wait.follow_up);
        false
    };

    if !function_ready {
        return Ok(JobEffects {
            reads,
            waits: waits.into_iter().collect(),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    if !world.require_activation_key_facts(root.function, &mut reads, &mut waits, &mut follow_up) {
        return Ok(JobEffects {
            reads,
            waits: waits.into_iter().collect(),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    let entry = ExecutableKey {
        activation: world.activation_key(root_id, root.function, &[]),
        need: root.need,
    };
    let entry_activation_fact = FactKey::Activation(entry.activation.clone());
    if world.fact_revision(entry_activation_fact.clone()).is_none() {
        waits.insert(entry_activation_fact);
        follow_up.insert(Job::SeedRoot(root_id));
    }
    let mut activations = HashSet::new();
    let mut executables = HashSet::new();
    let mut pending = VecDeque::new();
    if waits.is_empty() {
        pending.push_back(entry.clone());
    }

    while let Some(executable) = pending.pop_front() {
        let activation = executable.activation.clone();
        let activation_fact = FactKey::Activation(activation.clone());
        let activation_ready = read_fact(world, activation_fact, &mut reads, &mut dependencies, &mut waits);
        if !activation_ready {
            continue;
        }
        if !executables.insert(executable.clone()) {
            continue;
        }
        activations.insert(activation.clone());

        let analyzed_fact = FactKey::ActivationAnalyzed(activation.clone());
        let Some(analyzed_revision) = world.fact_revision(analyzed_fact.clone()) else {
            waits.insert(analyzed_fact);
            follow_up.insert(Job::AnalyzeActivation(activation.clone()));
            continue;
        };
        reads.push(analyzed_fact);
        dependencies.record(FactKey::ActivationAnalyzed(activation.clone()), analyzed_revision);
        let analysis = world
            .activation_analysis(&activation)
            .expect("activation analysis fact should have an analysis value")
            .clone();

        let return_fact = FactKey::ReturnType(activation.clone());
        let Some(return_revision) = world.fact_revision(return_fact.clone()) else {
            waits.insert(return_fact);
            follow_up.insert(Job::AnalyzeActivation(activation.clone()));
            continue;
        };
        reads.push(return_fact);
        dependencies.record(FactKey::ReturnType(activation.clone()), return_revision);

        let lowered_fact = FactKey::LoweredBody(activation.function);
        let Some(lowered_revision) = world.fact_revision(lowered_fact.clone()) else {
            waits.insert(lowered_fact);
            follow_up.insert(Job::LowerFunction(activation.function));
            continue;
        };
        reads.push(lowered_fact.clone());
        dependencies.record(lowered_fact, lowered_revision);

        let lowered_body = world.lowered_body(activation.function);
        let callsite_needs = executable_callsite_needs(&lowered_body, &analysis.reachable_clauses, executable.need);

        for latent in &analysis.latent_executables {
            if !executables.contains(latent) {
                pending.push_back(latent.clone());
            }
        }

        for callsite in analysis.callsites {
            let key = CallSiteKey {
                activation: activation.clone(),
                callsite,
            };
            let callsite_fact = FactKey::CallSiteSummary(key.clone());
            if !read_fact(world, callsite_fact, &mut reads, &mut dependencies, &mut waits) {
                follow_up.insert(Job::AnalyzeActivation(activation.clone()));
                continue;
            }
            let summary = world
                .callsite_summary(&key)
                .expect("callsite facts should have a summary value")
                .clone();
            let SelectedCallee::Function(function) = summary.callee else {
                continue;
            };
            if !world.require_activation_key_facts(function, &mut reads, &mut waits, &mut follow_up) {
                continue;
            }
            let need = callsite_needs
                .get(&callsite)
                .copied()
                .unwrap_or(super::super::identity::ExecutableNeed::Value);
            let callee_activation = world.activation_key(root_id, function, &summary.input_types);
            let callee_executable = ExecutableKey {
                activation: callee_activation.clone(),
                need,
            };
            let callee_activation_ready = read_fact(
                world,
                FactKey::Activation(callee_activation.clone()),
                &mut reads,
                &mut dependencies,
                &mut waits,
            );
            if !callee_activation_ready {
                follow_up.insert(Job::AnalyzeActivation(callee_activation));
                continue;
            }
            if !executables.contains(&callee_executable) {
                pending.push_back(callee_executable);
            }
        }
    }

    outputs.extend(
        executables
            .iter()
            .cloned()
            .map(|executable| (FactKey::Executable(executable), 1)),
    );

    if waits.is_empty() {
        let semantic_closed_fact = FactKey::SemanticClosed(root_id);
        let semantic_closed = world.define_semantic_closure(
            root_id,
            SemanticClosure {
                entry: entry.clone(),
                activations,
                executables,
            },
            dependencies,
        );
        let closure_changed = world.fact_would_change(semantic_closed_fact.clone(), semantic_closed);
        outputs.push((semantic_closed_fact, semantic_closed));
        if closure_changed {
            follow_up.insert(Job::MaterializeRoot(root_id));
        }
    }

    Ok(JobEffects {
        reads,
        waits: waits.into_iter().collect(),
        outputs,
        follow_up: follow_up.into_iter().collect(),
    })
}

fn read_fact(
    world: &World<'_>,
    fact: FactKey,
    reads: &mut Vec<FactKey>,
    dependencies: &mut DependencySnapshot,
    waits: &mut HashSet<FactKey>,
) -> bool {
    if let Some(revision) = world.fact_revision(fact.clone()) {
        reads.push(fact.clone());
        dependencies.record(fact, revision);
        true
    } else {
        waits.insert(fact);
        false
    }
}
