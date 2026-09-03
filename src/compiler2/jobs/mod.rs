//! Compiler2 job implementations grouped by private helper set.
//!
//! `drive.rs` owns the shared work vocabulary and drive loop. This module owns
//! the implementation bodies for current jobs and keeps their helper functions
//! private to the relevant job family.

use super::drive::{ExecutionContext, Job, JobEffects};
use super::scheduler::FatalError;

pub(crate) mod artifact;
pub(crate) mod backend;
mod body;
mod contract;
mod dispatch;
mod executable_facts;
mod keying;
mod macro_runtime;
mod native;
mod root;
pub(crate) mod runtime_demand;
mod semantic;
mod source;
#[cfg(test)]
mod source_test;
pub(crate) mod transport;
mod types;

pub(crate) fn run<T: crate::telemetry::RawSpanTelemetry>(
    context: &mut ExecutionContext<'_, T>,
    job: &Job,
) -> Result<JobEffects, FatalError> {
    let ExecutionContext { world, telemetry } = context;
    let tel = *telemetry;
    match job {
        Job::IndexCode(code_id) => source::index_code(world, tel, *code_id),
        Job::ScopeCode(code_id) => source::scope_code(world, tel, *code_id),
        Job::DefineModule(module_id) => source::define_module(world, tel, *module_id),
        Job::DefineModuleInterface(module_id) => source::define_module_interface(world, tel, *module_id),
        Job::PublishFunctionSource(function_id) => source::publish_function_source_job(world, tel, *function_id),
        Job::ExpandFunctionSource(function_id) => source::expand_function_source(world, tel, *function_id),
        Job::DefineFunction(function_id) => source::define_function(world, tel, *function_id),
        Job::DeriveTypeDef(type_name) => types::derive_type_def(world, tel, type_name),
        Job::DeriveFunctionContract(function_id) => contract::derive_function_contract(world, tel, *function_id),
        Job::LowerFunction(function_id) => body::lower_function(world, tel, *function_id),
        Job::ReifyGuardDispatch(function_id) => dispatch::reify_guard_dispatch(world, tel, *function_id),
        Job::PlanEntryDispatch(function_id) => dispatch::plan_entry_dispatch(world, tel, *function_id),
        Job::BuildMacroExecutable(function_id) => macro_runtime::build_macro_executable(world, tel, *function_id),
        Job::DeriveStaticCallees(function_id) => keying::derive_static_callees(world, tel, *function_id),
        Job::DeriveCallGraphComponent(function_id) => keying::derive_call_graph_component(world, *function_id),
        Job::DeriveDispatchMask(function_id) => keying::derive_dispatch_mask(world, tel, *function_id),
        Job::SeedRoot(root_id) => root::seed_root(world, tel, *root_id),
        Job::SeedActivation(activation) => root::seed_activation(world, tel, activation),
        Job::AnalyzeActivation(activation) => semantic::analyze_activation(world, tel, activation),
        Job::DeriveExecutableFacts(executable) => executable_facts::derive_executable_facts(world, executable),
        Job::BuildBackendProduct(root_id) => backend::build_backend_product(world, tel, *root_id),
        Job::LowerNativeProgram(root_id) => native::lower_native_program(world, tel, *root_id),
    }
}
