//! Compiler2 type-definition derivation jobs.
//!
//! `DeriveTypeDef` is strictly pulled: a `@type` that no reached consumer
//! references stays cold, exactly like an uncalled function. When pulled it
//! waits on the `TypeDefined` of every type its body names — the wait-set the
//! reference walk recorded — then resolves the body to a hard compiler2 type
//! and publishes it under the type's identity for consumers to read.

use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::identity::TypeName;
use super::super::scheduler::FatalError;
use super::super::world::World;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use std::collections::BTreeSet;

pub(super) fn derive_type_def(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    name: &TypeName,
) -> Result<JobEffects, FatalError> {
    let Some(decl) = world.type_decl(name).cloned() else {
        // The owning scope has not noted this name yet. Once its module is
        // defined, absence is a withdrawn declaration and this job must
        // conclude without its old TypeDefined claim. Before then, wait for the
        // scope that can note it.
        if name.module.is_global() || world.has_fact(&FactKey::ModuleDefined(name.module)) {
            return Ok(JobEffects {
                reads: current_uses([FactKey::TypeDeclared(name.clone())]),
                ..JobEffects::default()
            });
        }
        let mut effects = super::super::drive::ExecutionContext::new(world, tel).wait_for_type_decl(name.module);
        effects
            .reads
            .push(super::super::facts::FactUse::current(FactKey::TypeDeclared(
                name.clone(),
            )));
        return Ok(effects);
    };

    if let Some(component) = world.recursive_type_def_component(name) {
        if component.owner != *name {
            return Ok(JobEffects::default());
        }
        return derive_regular_component(world, tel, component.members);
    }

    // Wait on the `TypeDefined` of every type the body names before resolving.
    let refs = world.type_def_refs(name).to_vec();
    let declaration_reads = declaration_reads(name, &refs);
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
            reads: current_uses(declaration_reads),
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

    let mut reads = declaration_reads;
    reads.extend(refs.iter().map(|referenced| FactKey::TypeDefined(referenced.clone())));
    reads.extend(struct_refs.iter().map(|module| FactKey::StructDefined(*module)));
    let changed = super::super::drive::ExecutionContext::new(world, tel).define_type_def(name, def);
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

fn derive_regular_component(
    world: &mut World,
    tel: &impl crate::telemetry::Telemetry,
    component: Vec<TypeName>,
) -> Result<JobEffects, FatalError> {
    let members = component.iter().cloned().collect::<BTreeSet<_>>();
    let mut reads = component.iter().cloned().map(FactKey::TypeDeclared).collect::<Vec<_>>();
    let mut waits = Vec::new();
    for member in &component {
        for referenced in world.type_def_refs(member).iter().cloned() {
            let declaration = FactKey::TypeDeclared(referenced.clone());
            if !reads.contains(&declaration) {
                reads.push(declaration);
            }
            if !members.contains(&referenced) {
                let fact = FactKey::TypeDefined(referenced);
                if !world.has_fact(&fact) {
                    if !waits.contains(&fact) {
                        waits.push(fact);
                    }
                } else {
                    if !reads.contains(&fact) {
                        reads.push(fact);
                    }
                }
            }
        }
        for module in world.type_def_struct_refs(member).iter().copied() {
            let fact = FactKey::StructDefined(module);
            if !world.has_fact(&fact) {
                if !waits.contains(&fact) {
                    waits.push(fact);
                }
            } else {
                if !reads.contains(&fact) {
                    reads.push(fact);
                }
            }
        }
    }
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads: current_uses(reads),
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    let definitions = super::super::resolve::resolve_regular_type_defs(world, &component).map_err(|error| {
        emit_job_diagnostic(
            tel,
            Diagnostic::error(
                codes::RESOLVE_TYPE_ALIAS,
                format!("compiler2 could not resolve recursive type declarations: {}", error.msg),
                error.span,
            ),
        )
    })?;
    let mut changed = Vec::new();
    for (member, definition) in component.iter().zip(definitions) {
        if super::super::drive::ExecutionContext::new(world, tel).define_type_def(member, definition) {
            changed.push(FactKey::TypeDefined(member.clone()));
        }
    }
    Ok(JobEffects {
        reads: current_uses(reads),
        outputs: component.iter().cloned().map(FactKey::TypeDefined).collect(),
        changed,
        ..JobEffects::default()
    })
}

fn declaration_reads(name: &TypeName, refs: &[TypeName]) -> Vec<FactKey> {
    let mut declarations = BTreeSet::from([name.clone()]);
    declarations.extend(refs.iter().cloned());
    declarations.into_iter().map(FactKey::TypeDeclared).collect()
}

fn emit_job_diagnostic(tel: &impl crate::telemetry::Telemetry, diagnostic: Diagnostic) -> FatalError {
    emit_through(tel, &[diagnostic]);
    FatalError
}
