//! Compiler2 macro executable readiness.
//!
//! A macro executable is not a second body form. It is the ordinary
//! backend-ready artifact for a hidden compile-time root whose inputs are the
//! macro ABI: `__CALLER__` plus quoted arguments, all as `Any` values.

use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;

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
    let Some(backend_revision) = world.fact_revision(backend_fact.clone()) else {
        return Ok(JobEffects::wait_on_settled(
            backend_fact,
            [Job::SeedRoot(root), Job::LowerBackendProgram(root)],
        ));
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
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}
