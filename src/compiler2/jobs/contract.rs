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
use crate::type_expr::ResolvedSpecDecl;

use super::super::contract::FunctionContract;
use super::super::drive::{FactKey, Job, JobEffects};
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

    let (source, surface) = world.function_definition(function);
    let declared_specs = surface
        .attrs
        .iter()
        .filter_map(|attr| match attr {
            Attribute::Spec(spec) => Some(spec.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let specs = if !declared_specs.is_empty() {
        declared_specs
    } else if let Some(spec) = extern_semantic_contract(&surface) {
        vec![spec]
    } else {
        Vec::new()
    };

    let mut reads = vec![FactKey::FunctionDefined(function)];
    let mut waits = Vec::new();
    let mut follow_up = Vec::new();
    for referenced in world.function_type_refs(function).iter().cloned() {
        let fact = FactKey::TypeDefined(referenced.clone());
        if world.has_fact(&fact) {
            reads.push(fact);
        } else {
            waits.push(fact);
            follow_up.push(Job::DeriveTypeDef(referenced));
        }
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads,
            waits,
            follow_up,
            ..JobEffects::default()
        });
    }

    let contract = specs
        .iter()
        .map(|spec| world.resolve_spec_decl(source.namespace, spec))
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| {
            emit_job_diagnostic(
                world,
                Diagnostic::error(
                    codes::RESOLVE_TYPE_ALIAS,
                    format!(
                        "compiler2 could not resolve function contract for `{}`: {}",
                        surface.name, error.msg
                    ),
                    error.span,
                ),
            )
        })?;
    Ok(publish_contract(world, function, reads, contract))
}

fn publish_contract(
    world: &mut World<'_>,
    function: FunctionId,
    reads: Vec<FactKey>,
    contract: Vec<ResolvedSpecDecl<super::super::types::Ty>>,
) -> JobEffects {
    let revision = world.define_function_contract(function, FunctionContract::from_resolved(contract));
    JobEffects {
        reads,
        outputs: vec![(FactKey::FunctionContract(function), revision)],
        ..JobEffects::default()
    }
}

fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> FatalError {
    emit_through(world.tel(), None, &[diagnostic]);
    FatalError
}
