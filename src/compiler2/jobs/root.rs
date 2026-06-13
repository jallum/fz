use std::collections::HashSet;
use std::collections::VecDeque;

use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;

use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::{ExecutableKey, RootId, RootKind};
use super::super::scheduler::FatalError;
use super::super::semantic::{CallSiteKey, SelectedCallee, SemanticClosure};
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
    let mut reads = Vec::new();
    let mut waits = HashSet::new();
    let mut follow_up = Vec::new();
    let mut outputs = vec![root_fact];

    let function_fact = FactKey::FunctionDefined(root.function);
    let Some(_function_revision) = world.function_defined_revision(root.function) else {
        let wait = world.wait_for_function_definition(root.function);
        waits.extend(wait.waits.into_iter().map(|fact_use| fact_use.into_fact()));
        follow_up.extend(wait.follow_up);
        return Ok(JobEffects {
            reads: settled_uses(reads),
            waits: settled_uses(waits),
            outputs,
            follow_up,
            ..JobEffects::default()
        });
    };

    reads.push(function_fact);
    let (_, surface) = world.function_definition(root.function);
    if root.kind == RootKind::Runtime && surface.is_macro {
        return Err(emit_root_error(
            world,
            surface.span,
            format!(
                "compiler2 runtime root cannot target macro `{}/{}`",
                surface.name,
                surface.arity()
            ),
        ));
    }
    let mut gated_follow_up = HashSet::new();
    if !world.require_activation_key_facts(root.function, &mut reads, &mut waits, &mut gated_follow_up) {
        follow_up.extend(gated_follow_up);
        return Ok(JobEffects {
            reads: settled_uses(reads),
            waits: settled_uses(waits),
            outputs,
            follow_up,
            ..JobEffects::default()
        });
    }

    let entry_activation = world.activation_key(root_id, root.function, &root.input);
    let activation_fact = FactKey::Activation(entry_activation.clone());
    outputs.push(activation_fact);
    outputs.push(FactKey::ActivationInputs(entry_activation.clone()));
    outputs.push(FactKey::Executable(ExecutableKey {
        activation: entry_activation.clone(),
        need: root.need,
    }));
    follow_up.push(Job::LowerFunction(root.function));
    follow_up.push(Job::PlanEntryDispatch(root.function));
    follow_up.push(Job::AnalyzeActivation(entry_activation.clone()));
    follow_up.push(Job::SealSemanticClosure(root_id));
    Ok(JobEffects {
        reads: settled_uses(reads),
        outputs,
        activation_input_contributions: vec![(entry_activation, root.input.clone())],
        follow_up,
        ..JobEffects::default()
    })
}

fn emit_root_error(world: &World<'_>, span: Span, message: impl Into<String>) -> FatalError {
    let diagnostic = Diagnostic::error(codes::LOWER_UNSUPPORTED, message.into(), span);
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
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
    let mut changed = Vec::new();

    let root_fact = FactKey::RootEntry(root_id);
    if world.fact_is_settled(&root_fact) {
        reads.push(root_fact);
    } else {
        waits.insert(root_fact);
        follow_up.insert(Job::SeedRoot(root_id));
    }

    let function_fact = FactKey::FunctionDefined(root.function);
    let function_ready = if world.fact_is_settled(&function_fact) {
        reads.push(function_fact);
        true
    } else {
        let wait = world.wait_for_function_definition(root.function);
        waits.extend(wait.waits.into_iter().map(|fact_use| fact_use.into_fact()));
        follow_up.extend(wait.follow_up);
        false
    };

    if !function_ready {
        return Ok(JobEffects {
            reads: settled_uses(reads),
            waits: settled_uses(waits),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    if !world.require_activation_key_facts(root.function, &mut reads, &mut waits, &mut follow_up) {
        return Ok(JobEffects {
            reads: settled_uses(reads),
            waits: settled_uses(waits),
            follow_up: follow_up.into_iter().collect(),
            ..JobEffects::default()
        });
    }

    let entry = ExecutableKey {
        activation: world.activation_key(root_id, root.function, &root.input),
        need: root.need,
    };
    let entry_activation_fact = FactKey::Activation(entry.activation.clone());
    if !world.has_fact(&entry_activation_fact) {
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
        let activation_ready = read_fact(world, activation_fact, &mut reads, &mut waits);
        if !activation_ready {
            continue;
        }
        if !executables.insert(executable.clone()) {
            continue;
        }
        activations.insert(activation.clone());

        // Every gate here is a SETTLED gate, matching the `settled_uses`
        // registration below. Presence alone is not enough: a blocked
        // analyzer's claims stand (waiting extends, it cannot retract), so a
        // merely-present analysis may be a half-built snapshot. Settledness
        // is the freshness marker.
        let analyzed_fact = FactKey::ActivationAnalyzed(activation.clone());
        if !read_fact(world, analyzed_fact, &mut reads, &mut waits) {
            follow_up.insert(Job::AnalyzeActivation(activation.clone()));
            continue;
        }
        let analysis = world
            .activation_analysis(&activation)
            .expect("activation analysis fact should have an analysis value")
            .clone();

        let return_fact = FactKey::ReturnType(activation.clone());
        if !read_fact(world, return_fact, &mut reads, &mut waits) {
            follow_up.insert(Job::AnalyzeActivation(activation.clone()));
            continue;
        }

        let lowered_fact = FactKey::LoweredBody(activation.function);
        if !read_fact(world, lowered_fact.clone(), &mut reads, &mut waits) {
            follow_up.insert(Job::LowerFunction(activation.function));
            continue;
        }

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
            if !read_fact(world, callsite_fact, &mut reads, &mut waits) {
                follow_up.insert(Job::AnalyzeActivation(activation.clone()));
                continue;
            }
            let summary = world
                .callsite_summary(&key)
                .expect("callsite facts should have a summary value")
                .clone();
            for target in &summary.targets {
                let SelectedCallee::Function(function) = target.callee else {
                    continue;
                };
                if !world.require_activation_key_facts(function, &mut reads, &mut waits, &mut follow_up) {
                    continue;
                }
                let Some(callee_activation) = target.activation.clone() else {
                    return Err(FatalError);
                };
                let need = callsite_needs
                    .get(&callsite)
                    .copied()
                    .unwrap_or(super::super::identity::ExecutableNeed::Value);
                let callee_executable = ExecutableKey {
                    activation: callee_activation.clone(),
                    need,
                };
                let callee_activation_ready = read_fact(
                    world,
                    FactKey::Activation(callee_activation.clone()),
                    &mut reads,
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
    }

    outputs.extend(executables.iter().cloned().map(FactKey::Executable));

    if waits.is_empty() {
        let semantic_closed_fact = FactKey::SemanticClosed(root_id);
        let closure_changed = world.define_semantic_closure(
            root_id,
            SemanticClosure {
                entry,
                activations,
                executables,
            },
        );
        outputs.push(semantic_closed_fact.clone());
        if closure_changed {
            changed.push(semantic_closed_fact);
        }
        if closure_changed {
            follow_up.insert(Job::MaterializeRoot(root_id));
        }
    }

    Ok(JobEffects {
        reads: settled_uses(reads),
        waits: settled_uses(waits),
        outputs,
        changed,
        activation_input_contributions: Vec::new(),
        follow_up: follow_up.into_iter().collect(),
    })
}

fn read_fact(world: &World<'_>, fact: FactKey, reads: &mut Vec<FactKey>, waits: &mut HashSet<FactKey>) -> bool {
    if world.fact_is_settled(&fact) {
        reads.push(fact);
        true
    } else {
        waits.insert(fact);
        false
    }
}
