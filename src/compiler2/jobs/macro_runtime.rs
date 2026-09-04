//! Compiler2 macro executable readiness.
//!
//! A macro executable is not a second body form. It is the ordinary
//! backend-ready artifact for a hidden compile-time root whose inputs are the
//! macro ABI: `__CALLER__` plus quoted arguments, all as `Any` values.

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::source::Span;

use super::super::drive::{FactKey, JobEffects, settled_uses};
use super::super::identity::FunctionId;
use super::super::scheduler::FatalError;

pub(super) fn build_macro_executable(
    context: &mut super::super::drive::ExecutionContext<'_, impl crate::telemetry::RawSpanTelemetry>,
    function: FunctionId,
) -> Result<JobEffects, FatalError> {
    let Some(_) = context.world.function_defined_revision(function) else {
        return Ok(context.world.wait_for_function_definition(function));
    };
    let (_, surface) = context.world.function_definition(function);
    let (is_macro, span, name, arity) = (surface.is_macro, surface.span, surface.name.clone(), surface.arity());
    if !is_macro {
        return Err(emit_macro_runtime_error(
            context.telemetry,
            span,
            format!(
                "compiler2 cannot build a macro executable for non-macro `{}/{}`",
                name, arity
            ),
        ));
    }

    let root = context.world.macro_root(function);
    let backend_fact = FactKey::BackendProgram(root);
    if context.root_product_is_active(root) && !context.root_backend_is_projected(root) {
        return Ok(JobEffects::wait_on_current(backend_fact));
    }
    let program = if context.root_backend_is_projected(root) {
        context.world.backend_program(root)
    } else {
        super::backend::complete_backend_product(context, root)?
    };
    let backend_revision = context.world.fact_revision(&backend_fact).ok_or_else(|| {
        emit_macro_runtime_error(
            context.telemetry,
            span,
            format!(
                "compiler2 macro executable for `{}/{}` could not produce backend program",
                name, arity
            ),
        )
    })?;
    let changed = context.define_macro_executable(function, root, backend_revision, program);
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

fn emit_macro_runtime_error(
    tel: &impl crate::telemetry::Telemetry,
    span: Span,
    message: impl Into<String>,
) -> FatalError {
    let diagnostic = Diagnostic::error(codes::LOWER_UNSUPPORTED, message.into(), span);
    emit_through(tel, std::slice::from_ref(&diagnostic));
    FatalError
}
