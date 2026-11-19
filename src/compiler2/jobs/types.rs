//! Compiler2 type-definition derivation jobs.
//!
//! `DeriveTypeDef` is strictly pulled: a `@type` that no reached consumer
//! references stays cold, exactly like an uncalled function. When pulled it
//! waits on the `TypeDefined` of every type its body names — the wait-set the
//! reference walk recorded — then resolves the body to a hard compiler2 type
//! and publishes it under the type's identity for consumers to read.

use crate::diag::Diagnostic;
use crate::diag::codes;

use super::super::drive::{FactKey, JobEffects, current_uses, emit_job_diagnostic};
use super::super::identity::{NotedTypeDecl, TypeName};
use super::super::type_expr::TypeExprError;
use super::super::typedef::TypeDef;
use super::super::world::World;
use fz_engine::FatalError;

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

    // A type in a cycle of `@type`s that name each other cannot wait for a
    // member's definition, since that member waits for it in turn. Its job
    // resolves the whole cycle and publishes its own member; every member's
    // job reaches the same identities, so which runs first changes nothing.
    // It waits only on what lies outside the cycle.
    let cycle = world.type_def_cycle(name);
    let alone = [name.clone()];
    let members: &[TypeName] = if cycle.is_empty() { &alone } else { &cycle };
    let mut refs = Vec::new();
    let mut struct_refs = Vec::new();
    for member in members {
        for referenced in world.type_def_refs(member) {
            if !members.contains(referenced) && !refs.contains(referenced) {
                refs.push(referenced.clone());
            }
        }
        for module in world.type_def_struct_refs(member) {
            if !struct_refs.contains(module) {
                struct_refs.push(*module);
            }
        }
    }
    // A `%Mod{...}` in a body needs `Mod`'s precise field order before the
    // body can classify it (fz-rh2.17.5.6.10).
    let facts: Vec<FactKey> = refs
        .iter()
        .map(|referenced| FactKey::TypeDefined(referenced.clone()))
        .chain(struct_refs.iter().map(|module| FactKey::StructDefined(*module)))
        .collect();
    let waits: Vec<FactKey> = facts.iter().filter(|fact| !world.has_fact(fact)).cloned().collect();
    if !waits.is_empty() {
        return Ok(JobEffects {
            waits: current_uses(waits),
            ..JobEffects::default()
        });
    }

    let def = resolve_member(world, name, decl, &cycle).map_err(|error| {
        emit_job_diagnostic(tel, Diagnostic::error(codes::RESOLVE_TYPE_ALIAS, error.msg, error.span))
    })?;
    let changed = super::super::drive::ExecutionContext::new(world, tel).define_type_def(name, def);
    Ok(JobEffects {
        reads: current_uses(facts),
        outputs: vec![FactKey::TypeDefined(name.clone())],
        changed: changed
            .then_some(FactKey::TypeDefined(name.clone()))
            .into_iter()
            .collect(),
        ..JobEffects::default()
    })
}

/// `name`'s definition: its own body when it is in no cycle, otherwise its
/// member of `cycle` solved together.
fn resolve_member(
    world: &mut World,
    name: &TypeName,
    decl: NotedTypeDecl,
    cycle: &[TypeName],
) -> Result<TypeDef, TypeExprError> {
    if cycle.is_empty() {
        return world.resolve_type_def(name, &decl);
    }
    let noted: Vec<(TypeName, NotedTypeDecl)> = cycle
        .iter()
        .map(|member| {
            let decl = world
                .type_decl(member)
                .cloned()
                .expect("a cycle member's declaration is noted");
            (member.clone(), decl)
        })
        .collect();
    let index = cycle
        .iter()
        .position(|member| member == name)
        .expect("a type is in its own cycle");
    Ok(world.resolve_type_cycle(&noted)?.swap_remove(index))
}
