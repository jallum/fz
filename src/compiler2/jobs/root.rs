use std::collections::HashSet;

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::source::Span;

use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::{ActivationKey, ExecutableKey, ExecutableNeed, RootId, RootKind};
use super::super::scheduler::FatalError;
use super::super::semantic::RuntimeDemand;
use super::super::world::World;

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
    let entry_executable = ExecutableKey {
        activation: entry_activation.clone(),
        need: root.need,
    };
    outputs.push(FactKey::Executable(entry_executable.clone()));
    follow_up.push(Job::LowerFunction(root.function));
    follow_up.push(Job::PlanEntryDispatch(root.function));
    follow_up.push(Job::AnalyzeActivation(entry_activation.clone()));
    Ok(JobEffects {
        reads: settled_uses(reads),
        outputs,
        activation_input_contributions: vec![(entry_activation, root.input.clone())],
        return_demand_contributions: vec![(entry_executable, runtime_demand_for_need(root.need))],
        follow_up,
        ..JobEffects::default()
    })
}

fn runtime_demand_for_need(need: ExecutableNeed) -> RuntimeDemand {
    match need {
        ExecutableNeed::Value => RuntimeDemand::whole(),
        ExecutableNeed::TupleFields(arity) => RuntimeDemand::tuple_fields(vec![RuntimeDemand::whole(); arity]),
    }
}

/// Seeds the existence facts for a latent executable's activation — one reached
/// only through the runtime-demand frontier (an escaped or opaque callable, like
/// a reducer captured by a returned suspend continuation), never through a
/// direct call edge that an `analyze_activation` would publish.
///
/// This concludes (no waits), so `Activation` and `ActivationInputs` settle and
/// any consumer walking the runtime-demand frontier reaches the executable as an
/// ordinary settled callee. Seeding belongs in a concluding job: a *blocked*
/// publisher's claims never settle, so a job that both published and gated on a
/// latent activation would wait on its own perpetually-dirty output forever.
pub(super) fn seed_activation(world: &mut World<'_>, activation: &ActivationKey) -> Result<JobEffects, FatalError> {
    Ok(JobEffects {
        outputs: vec![
            FactKey::Activation(activation.clone()),
            FactKey::ActivationInputs(activation.clone()),
        ],
        activation_input_contributions: vec![(activation.clone(), activation.inputs(world.types()))],
        follow_up: vec![Job::AnalyzeActivation(activation.clone())],
        ..JobEffects::default()
    })
}

fn emit_root_error(world: &World<'_>, span: Span, message: impl Into<String>) -> FatalError {
    let diagnostic = Diagnostic::error(codes::LOWER_UNSUPPORTED, message.into(), span);
    emit_through(world.tel(), std::slice::from_ref(&diagnostic));
    FatalError
}
