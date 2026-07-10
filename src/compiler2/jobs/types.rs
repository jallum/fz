//! Compiler2 type-definition derivation jobs.
//!
//! `DeriveTypeDef` is strictly pulled: a `@type` that no reached consumer
//! references stays cold, exactly like an uncalled function. When pulled it
//! waits on the `TypeDefined` of every type its body names — the wait-set the
//! reference walk recorded — then resolves the body to a hard compiler2 type
//! and publishes it under the type's identity for consumers to read.

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;

use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::TypeName;
use super::super::scheduler::FatalError;
use super::super::world::World;

pub(super) fn derive_type_def(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    name: &TypeName,
) -> Result<JobEffects, FatalError> {
    let Some(decl) = world.type_decl(name).cloned() else {
        // The owning scope has not noted this name yet. A module type is noted
        // when its module is defined, so demand that and wait. A global name
        // that is still unnoted names no real `@type`: a recorded reference to
        // it would have required its scope to have already run, so its absence
        // here is an unresolved frontier, left cold without an output.
        if name.module.is_global() {
            return Ok(JobEffects::default());
        }
        return Ok(super::super::drive::ExecutionContext::new(world, tel).wait_for_type_decl(name.module));
    };

    // Wait on the `TypeDefined` of every type the body names before resolving.
    let refs = world.type_def_refs(name).to_vec();
    let mut waits = Vec::new();
    for referenced in &refs {
        if !world.has_fact(&FactKey::TypeDefined(referenced.clone())) {
            waits.push(FactKey::TypeDefined(referenced.clone()));
        }
    }
    // Same wait, `StructDefined` side: a `%Mod{...}` in this body needs
    // `Mod`'s precise field order before `resolve_type_def` can classify it
    // (fz-rh2.17.5.6.10).
    let struct_refs = world.type_def_struct_refs(name).to_vec();
    for module in &struct_refs {
        if !world.has_fact(&FactKey::StructDefined(*module)) {
            waits.push(FactKey::StructDefined(*module));
        }
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    let def = world.resolve_type_def(name, &decl).map_err(|error| {
        emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::RESOLVE_TYPE_ALIAS,
                format!("compiler2 could not resolve type `{}`: {}", name.name, error.msg),
                error.span,
            ),
        )
    })?;

    let mut reads: Vec<_> = refs
        .iter()
        .map(|referenced| FactKey::TypeDefined(referenced.clone()))
        .collect();
    reads.extend(struct_refs.iter().map(|module| FactKey::StructDefined(*module)));
    let changed = super::super::drive::ExecutionContext::new(world, tel).define_type_def(name.clone(), def);
    Ok(JobEffects {
        reads: current_uses(reads),
        outputs: vec![FactKey::TypeDefined(name.clone())],
        changed: changed
            .then_some(FactKey::TypeDefined(name.clone()))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

fn emit_job_diagnostic(tel: &impl crate::telemetry::Telemetry, diagnostic: Diagnostic) -> FatalError {
    emit_through(tel, &[diagnostic]);
    FatalError
}
