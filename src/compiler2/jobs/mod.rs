//! Compiler2 job implementations grouped by private helper set.
//!
//! `drive.rs` owns the shared work vocabulary and drive loop. This module owns
//! the implementation bodies for current jobs and keeps their helper functions
//! private to the relevant job family.

use super::drive::{Job, JobEffects};
use super::scheduler::FatalError;
use super::world::World;

mod artifact;
mod backend;
mod body;
mod dispatch;
mod keying;
mod native;
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
        Job::DeriveRecursive(function_id) => keying::derive_recursive(world, *function_id),
        Job::DeriveDispatchMask(function_id) => keying::derive_dispatch_mask(world, *function_id),
        Job::SeedRoot(root_id) => root::seed_root(world, *root_id),
        Job::AnalyzeActivation(activation) => semantic::analyze_activation(world, activation),
        Job::SealSemanticClosure(root_id) => root::seal_semantic_closure(world, *root_id),
        Job::MaterializeRoot(root_id) => artifact::materialize_root(world, *root_id),
        Job::DeriveAbiReady(root_id) => artifact::derive_abi_ready(world, *root_id),
        Job::DeriveEmissionReady(root_id) => artifact::derive_emission_ready(world, *root_id),
        Job::LowerBackendProgram(root_id) => backend::lower_backend_program(world, *root_id),
        Job::LowerNativeProgram(root_id) => native::lower_native_program(world, *root_id),
    }
}
