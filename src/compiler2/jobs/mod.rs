//! Compiler2 job implementations grouped by private helper set.
//!
//! `drive.rs` owns the shared work vocabulary and drive loop. This module owns
//! the implementation bodies for current jobs and keeps their helper functions
//! private to the relevant job family.

use super::drive::{Job, JobEffects};
use super::scheduler::FatalError;
use super::world::World;

mod root;
mod source;

pub(crate) fn run(world: &mut World<'_>, job: &Job) -> Result<JobEffects, FatalError> {
    match job {
        Job::IndexCode(code_id) => source::index_code(world, *code_id),
        Job::ScopeCode(code_id) => source::scope_code(world, *code_id),
        Job::DefineModule(module_id) => source::define_module(world, *module_id),
        Job::SeedRoot(root_id) => root::seed_root(world, *root_id),
        Job::CheckSemanticClosure(root_id) => root::check_semantic_closure(world, *root_id),
    }
}
