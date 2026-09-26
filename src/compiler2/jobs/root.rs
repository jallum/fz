use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::source::Span;

use super::super::drive::{FactKey, JobEffects, settled_uses};
use super::super::identity::{ActivationKey, ExecutableKey, RootId, RootKind};
use super::super::scheduler::FatalError;
use super::super::semantic::{RuntimeDemand, TargetDemandContribution};
use super::super::world::World;

/// The facts `seed_root` cannot conclude without: the entry function's
/// definition, then the two facts `activation_key` reads to mint the entry
/// activation. Both rungs are named from the root alone, so the scheduler
/// checks them before ever starting a never-run `SeedRoot`
/// (`Job::missing_gates`).
pub(super) fn seed_root_gates(world: &World, root_id: RootId) -> Vec<FactKey> {
    let function = world.root_entry(root_id).function;
    if world.function_defined_revision(function).is_none() {
        return vec![FactKey::FunctionDefined(function)];
    }
    let mut gates = Vec::new();
    if !world.has_fact(&FactKey::Recursive(function)) {
        gates.push(FactKey::Recursive(function));
    }
    if !world.has_fact(&FactKey::InputDemand(function)) {
        gates.push(FactKey::InputDemand(function));
    }
    gates
}

/// Seeds one semantic root once its entry definition exists.
///
/// A root entry is compiler-owned and can exist before the function does. The
/// seed publishes the root fact immediately, then waits until the entry
/// function is defined before it schedules the first closure walk.
pub(super) fn seed_root(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
) -> Result<JobEffects, FatalError> {
    let root = world.root_entry(root_id);
    let root_fact = FactKey::RootEntry(root_id);
    let mut outputs = vec![root_fact];

    let gates = seed_root_gates(world, root_id);
    if !gates.is_empty() {
        return Ok(JobEffects {
            waits: settled_uses(gates),
            outputs,
            ..JobEffects::default()
        });
    }

    let mut reads = vec![FactKey::FunctionDefined(root.function)];
    let (_, surface) = world.function_definition(root.function);
    if root.kind == RootKind::Runtime && surface.is_macro {
        return Err(emit_root_error(
            tel,
            surface.span,
            format!(
                "compiler2 runtime root cannot target macro `{}/{}`",
                surface.name,
                surface.arity()
            ),
        ));
    }
    if root.kind == RootKind::Macro && !surface.is_macro {
        return Err(emit_root_error(
            tel,
            surface.span,
            format!(
                "compiler2 macro root target `{}/{}` is not a macro",
                surface.name,
                surface.arity()
            ),
        ));
    }
    reads.push(FactKey::Recursive(root.function));
    reads.push(FactKey::InputDemand(root.function));

    let entry_activation = world.activation_key(root_id, root.function, &root.input);
    let activation_fact = FactKey::Activation(entry_activation.clone());
    outputs.push(activation_fact);
    outputs.push(FactKey::ActivationInputs(entry_activation.clone()));
    let entry_executable = ExecutableKey {
        activation: entry_activation.clone(),
        need: root.need,
    };
    outputs.push(FactKey::Executable(entry_executable.clone()));
    // LowerFunction/PlanEntryDispatch are not re-emitted here: reaching this
    // point means `seed_root_gates` above already observed both
    // `Recursive(function)` and `InputDemand(function)` present, and their
    // producers (`derive_call_graph_component`, `derive_input_demand`) only
    // conclude after `LoweredBody`/`EntryDispatch` exist -- so those jobs have
    // already run. First-run demand for them lives in
    // DeriveCallGraphComponent/DeriveInputDemand; later change waves reach
    // them via the normal wake mechanism.
    //
    // `AnalyzeActivation` is not pushed either. Publishing `Activation(entry)`
    // above records the same standing frontier edge as caller-discovered
    // callees; `demand_activation_frontier_analyses` expands it through the
    // fact->producer map on both the bare drive and product fact-wait paths.
    Ok(JobEffects {
        reads: settled_uses(reads),
        outputs,
        activation_input_contributions: vec![(entry_activation, root.input.clone())],
        runtime_demand_input_contributions: vec![(
            entry_executable,
            TargetDemandContribution {
                return_demand: Some(RuntimeDemand::for_executable_need(root.need)),
                ..TargetDemandContribution::default()
            },
        )],
        ..JobEffects::default()
    })
}

/// Seeds the existence facts for a latent executable's activation — one reached
/// only through the runtime-demand frontier (an escaped or opaque callable, like
/// a reducer captured by a returned suspend continuation), never through a
/// direct call edge that an `analyze_activation` would publish.
///
/// The input row is RECONSTRUCTED from the key's own arrow, which is the truth
/// only for such a key: nothing else ever described it. That is why
/// `World::seed_activation_producer` routes a demand here only while
/// `ActivationInputs` has no publisher — for an activation some caller
/// discovered, this reconstruction would fabricate that caller's evidence and
/// undo the caller's own withdrawal of the key (fz-kdt.69.1).
///
/// This concludes (no waits), so `Activation` and `ActivationInputs` settle and
/// any consumer walking the runtime-demand frontier reaches the executable as an
/// ordinary settled callee. Seeding belongs in a concluding job: a *blocked*
/// publisher's claims never settle, so a job that both published and gated on a
/// latent activation would wait on its own perpetually-dirty output forever.
///
/// `AnalyzeActivation` is not pushed as a follow-up: this job is itself only
/// ever demanded by `World::demand_fact_producer`'s `Activation`/
/// `ActivationInputs`, `ActivationAnalyzed`/`ReturnType`, or
/// `CallSiteSummary`/`CallSiteTargets` arms, and every one of those arms that
/// reaches here also demands `AnalyzeActivation` for this same activation in
/// the very same call -- co-demanded, not chained through a push. First-run
/// demand is genuinely pulled by whichever fact wait triggered the seed.
pub(super) fn seed_activation(
    world: &mut World,
    _tel: &impl crate::telemetry::Telemetry,
    activation: &ActivationKey,
) -> Result<JobEffects, FatalError> {
    Ok(JobEffects {
        outputs: vec![
            FactKey::Activation(activation.clone()),
            FactKey::ActivationInputs(activation.clone()),
        ],
        activation_input_contributions: vec![(activation.clone(), activation.inputs(world.types()))],
        ..JobEffects::default()
    })
}

fn emit_root_error(tel: &impl crate::telemetry::Telemetry, span: Span, message: impl Into<String>) -> FatalError {
    let diagnostic = Diagnostic::error(codes::LOWER_UNSUPPORTED, message.into(), span);
    emit_through(tel, std::slice::from_ref(&diagnostic));
    FatalError
}
