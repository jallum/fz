//! Compiler2 job implementations grouped by private helper set.
//!
//! `drive.rs` owns the shared work vocabulary and drive loop. This module owns
//! the implementation bodies for current jobs and keeps their helper functions
//! private to the relevant job family.

use super::drive::{Job, JobEffects};
use super::scheduler::FatalError;
use super::world::World;

mod body;
mod dispatch;
mod root;
mod semantic;
mod source;

pub(crate) fn run(world: &mut World<'_>, job: &Job) -> Result<JobEffects, FatalError> {
    match job {
        Job::IndexCode(code_id) => source::index_code(world, *code_id),
        Job::ScopeCode(code_id) => source::scope_code(world, *code_id),
        Job::DefineModule(module_id) => source::define_module(world, *module_id),
        Job::LowerFunction(function_id) => body::lower_function(world, *function_id),
        Job::ReifyGuardDispatch(function_id) => dispatch::reify_guard_dispatch(world, *function_id),
        Job::PlanEntryDispatch(function_id) => dispatch::plan_entry_dispatch(world, *function_id),
        Job::SeedRoot(root_id) => root::seed_root(world, *root_id),
        Job::AnalyzeActivation(activation) => semantic::analyze_activation(world, activation),
        Job::CheckSemanticClosure(root_id) => root::check_semantic_closure(world, *root_id),
    }
}
