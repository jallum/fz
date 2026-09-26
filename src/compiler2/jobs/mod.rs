//! Compiler2 job implementations grouped by private helper set.
//!
//! `drive.rs` owns the shared work vocabulary and drive loop. This module owns
//! the implementation bodies for current jobs and keeps their helper functions
//! private to the relevant job family.

use super::drive::{ExecutionContext, FactKey, Job, JobEffects};
use super::scheduler::FatalError;
use super::world::World;

pub(crate) mod artifact;
pub(crate) mod backend;
mod body;
#[cfg(test)]
mod body_test;
mod callable_target;
mod contract;
mod dispatch;
mod executable_facts;
mod keying;
mod native;
pub(super) use native::produce_native_program;
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
    let ExecutionContext {
        world,
        telemetry,
        product_sessions,
    } = context;
    let tel = *telemetry;
    match job {
        Job::IndexCode(source_owner) => source::index_code(world, tel, *source_owner),
        Job::ScopeCode(source_owner) => source::scope_code(world, tel, product_sessions.as_deref(), *source_owner),
        Job::DefineModule(module_id) => source::define_module(world, tel, product_sessions.as_deref(), *module_id),
        Job::DefineModuleInterface(module_id) => source::define_module_interface(world, tel, *module_id),
        Job::ExpandFunctionSource(function_id) => {
            source::expand_function_source(world, tel, product_sessions.as_deref(), *function_id)
        }
        Job::DefineFunction(function_id) => source::define_function(world, tel, *function_id),
        Job::DeriveTypeDef(type_name) => types::derive_type_def(world, tel, type_name),
        Job::DeriveFunctionContract(function_id) => contract::derive_function_contract(world, tel, *function_id),
        Job::LowerFunction(function_id) => body::lower_function(world, tel, *function_id),
        Job::ReifyGuardDispatch(function_id) => dispatch::reify_guard_dispatch(world, tel, *function_id),
        Job::PlanEntryDispatch(function_id) => dispatch::plan_entry_dispatch(world, tel, *function_id),
        Job::DeriveStaticCallees(function_id) => keying::derive_static_callees(world, *function_id),
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

impl Job {
    /// The facts this job cannot conclude without, given its subject and the
    /// facts already present -- current or settled, as each gate's own
    /// derivation decides. Empty means every gate is satisfied, or this kind
    /// declares none.
    ///
    /// The scheduler calls this once, before ever starting a never-run job
    /// (`World::demand_producer_if_needed`), and redirects demand to each
    /// missing gate's own producer instead of starting the job to discover
    /// the same fact missing from inside its body. A job kind absent from the
    /// match below has no gate: it starts the moment anything demands its
    /// output, exactly as before this method existed.
    ///
    /// A wait a job's body discovers only while it runs -- a callee reached
    /// by walking a graph, a macro found mid-expansion -- is never a gate: a
    /// gate is nameable from the subject alone, before the job has read
    /// anything.
    pub(crate) fn missing_gates(&self, world: &mut World) -> Vec<FactKey> {
        match self {
            Job::SeedRoot(root_id) => root::seed_root_gates(world, *root_id),
            Job::DefineFunction(function_id) => source::define_function_gates(world, *function_id),
            Job::ExpandFunctionSource(function_id) => source::expand_function_source_gates(world, *function_id),
            Job::ScopeCode(source_owner) => source::scope_code_gates(world, *source_owner),
            Job::DeriveInputDemand(function_id) => keying::derive_input_demand_gates(world, *function_id),
            Job::DeriveCallGraphComponent(function_id) => {
                keying::derive_call_graph_component_gates(world, *function_id)
            }
            Job::DeriveRuntimeDemand(executable) => runtime_demand::derive_runtime_demand_gates(world, executable),
            Job::LowerFunction(function_id) => body::lower_function_gates(world, *function_id),
            Job::DeriveStaticCallees(function_id) => keying::derive_static_callees_gates(world, *function_id),
            Job::IndexCode(_)
            | Job::DefineModule(_)
            | Job::DefineModuleInterface(_)
            | Job::DeriveTypeDef(_)
            | Job::DeriveFunctionContract(_)
            | Job::ReifyGuardDispatch(_)
            | Job::PlanEntryDispatch(_)
            | Job::SeedActivation(_)
            | Job::AnalyzeActivation(_)
            | Job::DeriveExecutableFacts(_)
            | Job::DeriveCallableConstructionTarget(_) => Vec::new(),
        }
    }
}
