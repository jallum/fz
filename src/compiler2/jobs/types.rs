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

use super::super::drive::{FactKey, Job, JobEffects};
use super::super::identity::TypeName;
use super::super::scheduler::FatalError;
use super::super::world::World;

pub(super) fn derive_type_def(world: &mut World<'_>, name: &TypeName) -> Result<JobEffects, FatalError> {
    if let Some(def) = world.protocol_domain_type_def(name) {
        let revision = world.define_type_def(name.clone(), def);
        return Ok(JobEffects {
            outputs: vec![(FactKey::TypeDefined(name.clone()), revision)],
            ..JobEffects::default()
        });
    }

    let Some(decl) = world.type_decl(name).cloned() else {
        // The owning scope has not noted this name yet. A module type is noted
        // when its module is defined, so demand that and wait. A global name
        // that is still unnoted names no real `@type`: a recorded reference to
        // it would have required its scope to have already run, so its absence
        // here is an unresolved frontier, left cold without an output.
        if name.module.is_global() {
            return Ok(JobEffects::default());
        }
        return Ok(world.wait_for_type_decl(name.module));
    };

    // Wait on the `TypeDefined` of every type the body names before resolving.
    let refs = world.type_def_refs(name).to_vec();
    let mut waits = Vec::new();
    let mut follow_up = Vec::new();
    for referenced in &refs {
        if !world.has_fact(&FactKey::TypeDefined(referenced.clone())) {
            waits.push(FactKey::TypeDefined(referenced.clone()));
            follow_up.push(Job::DeriveTypeDef(referenced.clone()));
        }
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            waits,
            follow_up,
            ..JobEffects::default()
        });
    }

    let def = world.resolve_type_def(name, &decl).map_err(|error| {
        emit_job_diagnostic(
            world,
            Diagnostic::error(
                codes::RESOLVE_TYPE_ALIAS,
                format!("compiler2 could not resolve type `{}`: {}", name.name, error.msg),
                error.span,
            ),
        )
    })?;

    let reads = refs
        .iter()
        .map(|referenced| FactKey::TypeDefined(referenced.clone()))
        .collect();
    let revision = world.define_type_def(name.clone(), def);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::TypeDefined(name.clone()), revision)],
        ..JobEffects::default()
    })
}

fn emit_job_diagnostic(world: &World<'_>, diagnostic: Diagnostic) -> FatalError {
    emit_through(world.tel(), None, &[diagnostic]);
    FatalError
}
