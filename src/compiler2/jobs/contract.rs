//! Compiler2 function-contract derivation jobs.
//!
//! A contract is the callee-owned declared surface for one function. Semantic
//! call resolution consumes it to refine observed arguments before waking
//! activations or callable-boundary demand.

use crate::ast::Attribute;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::ir_lower::extern_semantic_contract;
use crate::type_expr::{ResolvedSpecDecl, resolve_spec_decls_generic};

use super::super::contract::FunctionContract;
use super::super::drive::{FactKey, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::FunctionId;
use super::super::scheduler::FatalError;
use super::super::world::World;

pub(super) fn derive_function_contract(world: &mut World<'_>, function: FunctionId) -> Result<JobEffects, FatalError> {
    let Some(_) = world.function_defined_revision(function) else {
        return Ok(world.wait_for_function_definition(function));
    };
    if !world.function_declares_contract(function) {
        return Ok(JobEffects::default());
    }

    let def = world.function_definition(function);
    let declared_specs = def
        .ast
        .attrs
        .iter()
        .filter_map(|attr| match attr {
            Attribute::Spec(spec) => Some(spec.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let specs = if !declared_specs.is_empty() {
        declared_specs
    } else if let Some(spec) = extern_semantic_contract(&def.ast) {
        vec![spec]
    } else {
        Vec::new()
    };
    let type_env = world.function_type_env(function).map_err(|error| {
        emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::RESOLVE_TYPE_ALIAS,
                format!(
                    "compiler2 could not resolve function contract for `{}`: {}",
                    def.ast.name, error.msg
                ),
                error.span,
            ),
        )
    })?;
    let contract = resolve_spec_decls_generic(world.types_mut(), specs.iter(), &type_env).map_err(|error| {
        emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::RESOLVE_TYPE_ALIAS,
                format!(
                    "compiler2 could not resolve function contract for `{}`: {}",
                    def.ast.name, error.msg
                ),
                error.span,
            ),
        )
    })?;
    Ok(publish_contract(
        world,
        function,
        FactKey::FunctionDefined(function),
        contract,
    ))
}

fn publish_contract(
    world: &mut World<'_>,
    function: FunctionId,
    read: FactKey,
    contract: Vec<ResolvedSpecDecl<super::super::types::Ty>>,
) -> JobEffects {
    let revision = world.define_function_contract(function, FunctionContract::from_resolved(contract));
    JobEffects {
        reads: vec![read],
        outputs: vec![(FactKey::FunctionContract(function), FactValue::presence(revision))],
        ..JobEffects::default()
    }
}

fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> FatalError {
    emit_through(world.tel(), None, &[diagnostic]);
    FatalError
}
