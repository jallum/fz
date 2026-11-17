//! A submitted source's declarations are checked because the source wrote
//! them, not because something reaches them.
//!
//! `CheckDeclarations` reads the indexed surface to find which parts of the
//! source declare something, and waits on the facts the reached path would
//! have asked for: the source's own scope if its top level declares, each
//! declaring module defined, then each function that declares a contract has
//! its contract derived and each `@type` has its type defined. Those jobs carry
//! every diagnostic; this one only asks. A source or module that declares
//! nothing is never scoped or defined for it, and it never asks for a lowered
//! body, so a function nothing calls stays cold past its contract.

use super::super::code::SourceOwner;
use super::super::drive::{FactKey, JobEffects, current_uses};
use super::super::world::World;
use fz_engine::FatalError;

/// Which parts of a source declare something is known once it is indexed.
pub(super) fn check_declarations_gates(world: &World, owner: SourceOwner) -> Vec<FactKey> {
    let indexed = FactKey::CodeIndexed(owner);
    if world.has_fact(&indexed) {
        Vec::new()
    } else {
        vec![indexed]
    }
}

pub(super) fn check_declarations(world: &mut World, owner: SourceOwner) -> Result<JobEffects, FatalError> {
    if let Some(gate) = check_declarations_gates(world, owner).into_iter().next() {
        return Ok(JobEffects::wait_on_current(gate));
    }
    let mut asked = vec![FactKey::CodeIndexed(owner)];
    if world.code_writes_declarations(owner) {
        asked.push(FactKey::CodeScoped(owner));
    }
    asked.extend(defined_modules(world, owner));
    if let Some(waits) = missing(world, &asked) {
        return Ok(waits);
    }
    asked.extend(declarations(world, owner));
    if let Some(waits) = missing(world, &asked) {
        return Ok(waits);
    }
    Ok(JobEffects {
        reads: current_uses(asked),
        outputs: vec![FactKey::DeclarationsChecked(owner)],
        ..JobEffects::default()
    })
}

/// Every module the source writes that declares something, defined: a
/// module's own functions and types are noted only as it is defined. A module
/// that declares nothing stays cold.
fn defined_modules(world: &World, owner: SourceOwner) -> Vec<FactKey> {
    world
        .source_declarations(owner)
        .map(|declared| {
            declared
                .modules
                .iter()
                .filter(|module| world.module_writes_declarations(**module))
                .map(|module| FactKey::ModuleDefined(*module))
                .collect()
        })
        .unwrap_or_default()
}

/// The contract of every function that declares one, and the definition of
/// every `@type`. A protocol's callbacks are never defined themselves; their
/// signatures are read through the protocol.
fn declarations(world: &World, owner: SourceOwner) -> Vec<FactKey> {
    let Some(declared) = world.source_declarations(owner) else {
        return Vec::new();
    };
    let contracts = declared
        .functions
        .iter()
        .filter(|function| {
            world.function_declares_contract(**function) && world.protocol_callback(**function).is_none()
        })
        .map(|function| FactKey::FunctionContract(*function));
    let types = declared.types.iter().map(|name| FactKey::TypeDefined(name.clone()));
    contracts.chain(types).collect()
}

/// The waits for whichever of `facts` are not yet present, if any are not.
fn missing(world: &World, facts: &[FactKey]) -> Option<JobEffects> {
    let waits: Vec<FactKey> = facts.iter().filter(|fact| !world.has_fact(fact)).cloned().collect();
    (!waits.is_empty()).then(|| JobEffects {
        waits: current_uses(waits),
        ..JobEffects::default()
    })
}

#[cfg(test)]
#[path = "declarations_test.rs"]
mod declarations_test;
