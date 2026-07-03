//! Compiler2 macro executable readiness.
//!
//! A macro executable is not a second body form. It is the ordinary
//! backend-ready artifact for a hidden compile-time root whose inputs are the
//! macro ABI: `__CALLER__` plus quoted arguments, all as `Any` values.

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::source::Span;

use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::FunctionId;
use super::super::scheduler::FatalError;
use super::super::world::World;

pub(super) fn build_macro_executable(world: &mut World<'_>, function: FunctionId) -> Result<JobEffects, FatalError> {
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };
    let (_, surface) = world.function_definition(function);
    if !surface.is_macro {
        return Err(emit_macro_runtime_error(
            world,
            surface.span,
            format!(
                "compiler2 cannot build a macro executable for non-macro `{}/{}`",
                surface.name,
                surface.arity()
            ),
        ));
    }

    let root = world.macro_root(function);
    let backend_fact = FactKey::BackendProgram(root);
    // `BackendProgram` is a co-output-only fact (`World::demand_fact_producer`,
    // drive.rs): it has no arm in the fact->producer map, so returning
    // `wait_on_current(backend_fact)` here would name a fact nothing can ever
    // be demanded to produce, i.e. a permanent stall rather than a resumable
    // wait. Its one real producer is the already-sanctioned bounded
    // product-pull driver (`drive_root_backend_product`, product_drive.rs) --
    // the same self-contained inner pull-drive `Compiler2::run_root_interp`
    // and `product_drive::drive_product_fact_wait` already run synchronously
    // to completion (see "Product pulls for artifacts",
    // .agent/docs/fact-engine.md). Calling it inline and registering its
    // result through `complete_job` is invoking that sanctioned mechanism
    // directly, not commanding an unrelated job to run out of turn:
    // `Job::BuildBackendProduct` is never enqueued on the agenda in
    // production (only `world.demand` in tests seeds it there); it exists
    // solely as the claim identity `complete_job` needs to register the
    // pull-driver's result into the fact table. `jobs::lower_native_program`
    // (jobs/native.rs) does the identical inline pull for the same fact and
    // the same reason: both jobs need one root's `BackendProgram` as an
    // ordinary prerequisite of their own conclusion, and that fact's sole
    // producer is a bounded product-drive, not another agenda job.
    let backend_revision = match world.fact_revision(&backend_fact) {
        Some(revision) => revision,
        None => {
            let effects = super::backend::build_backend_product(world, root)?;
            world.complete_job(Job::BuildBackendProduct(root), effects);
            world.fact_revision(&backend_fact).ok_or_else(|| {
                emit_macro_runtime_error(
                    world,
                    surface.span,
                    format!(
                        "compiler2 macro executable for `{}/{}` could not produce backend program",
                        surface.name,
                        surface.arity()
                    ),
                )
            })?
        }
    };

    let program = world.backend_program(root);
    let changed = world.define_macro_executable(function, root, backend_revision, program);
    Ok(JobEffects {
        reads: settled_uses([FactKey::FunctionDefined(function), backend_fact]),
        outputs: vec![FactKey::MacroExecutable(function)],
        changed: changed
            .then_some(FactKey::MacroExecutable(function))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

fn emit_macro_runtime_error(world: &World<'_>, span: Span, message: impl Into<String>) -> FatalError {
    let diagnostic = Diagnostic::error(codes::LOWER_UNSUPPORTED, message.into(), span);
    emit_through(world.tel(), std::slice::from_ref(&diagnostic));
    FatalError
}
