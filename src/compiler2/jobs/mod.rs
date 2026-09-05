//! Compiler2 job implementations grouped by private helper set.
//!
//! `drive.rs` owns the shared work vocabulary and drive loop. This module owns
//! the implementation bodies for current jobs and keeps their helper functions
//! private to the relevant job family.

use super::drive::{ExecutionContext, Job, JobEffects};
use super::scheduler::FatalError;

pub(crate) fn lower_native_program_for_request<T: crate::telemetry::RawSpanTelemetry>(
    context: &mut ExecutionContext<'_, T>,
    root: super::identity::RootId,
    timeout: Option<std::time::Duration>,
) -> Result<std::rc::Rc<super::NativeProgram>, String> {
    native::lower_native_program_for_request(context, root, timeout)
}

pub(crate) mod artifact;
pub(crate) mod backend;
mod body;
mod callable_target;
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
    match job {
        Job::BuildMacroExecutable(function_id) => return macro_runtime::build_macro_executable(context, *function_id),
        Job::BuildBackendProduct(root_id) => return backend::build_backend_product(context, *root_id),
        Job::LowerNativeProgram(root_id) => return native::lower_native_program(context, *root_id),
        _ => {}
    }
    let ExecutionContext { world, telemetry, .. } = context;
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
        Job::BuildMacroExecutable(_) | Job::BuildBackendProduct(_) | Job::LowerNativeProgram(_) => {
            unreachable!("context-owning jobs return before the ordinary dispatch")
        }
        Job::DeriveStaticCallees(function_id) => keying::derive_static_callees(world, tel, *function_id),
        Job::DeriveCallGraphComponent(function_id) => keying::derive_call_graph_component(world, *function_id),
        Job::DeriveInputDemand(function_id) => keying::derive_input_demand(world, tel, *function_id),
        Job::SeedRoot(root_id) => root::seed_root(world, tel, *root_id),
        Job::SeedActivation(activation) => root::seed_activation(world, tel, activation),
        Job::AnalyzeActivation(activation) => semantic::analyze_activation(world, tel, activation),
        Job::DeriveExecutableFacts(executable) => executable_facts::derive_executable_facts(world, executable),
        Job::DeriveCallableConstructionTarget(key) => callable_target::derive(world, key),
        Job::DeriveRuntimeDemand(executable) => runtime_demand::derive_runtime_demand_fact(world, tel, executable),
    }
}
