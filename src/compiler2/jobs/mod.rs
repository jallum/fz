//! Compiler2 job implementations grouped by private helper set.
//!
//! `drive.rs` owns the shared work vocabulary and drive loop. This module owns
//! the implementation bodies for current jobs and keeps their helper functions
//! private to the relevant job family.

use super::drive::{ExecutionContext, FactKey, Job, JobEffects, current_uses, settled_uses};
use super::world::{JobRetirement, RetirementGround, World};
use fz_engine::FactUse;
use fz_engine::FatalError;

pub(crate) mod artifact;
pub(crate) mod backend;
mod body;
#[cfg(test)]
mod body_test;
mod callable_target;
mod capture_owners;
mod contract;
mod declarations;
mod dispatch;
pub(super) use dispatch::is_guard_expr;
mod executable_facts;
mod frame_free;
mod keying;
mod native;
mod reach;
pub(super) use native::produce_native_program;
pub(super) use semantic::callees_awaiting_their_module;
mod root;
pub(crate) mod runtime_demand;
mod scope;
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
    if let Some(retired) = retire_ungrounded(context, job) {
        return Ok(retired);
    }
    let ExecutionContext {
        world,
        telemetry,
        product_sessions,
    } = context;
    let tel = *telemetry;
    match job {
        Job::IndexCode(source_owner) => source::index_code(world, tel, *source_owner),
        Job::ScopeCode(source_owner) => source::scope_code(world, tel, product_sessions.as_deref(), *source_owner),
        Job::CheckDeclarations(source_owner) => declarations::check_declarations(world, *source_owner),
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
        Job::DeriveRecursive(function_id) => keying::derive_recursive(world, *function_id),
        Job::DeriveStaticReach(function_id) => reach::derive_static_reach(world, *function_id),
        Job::DeriveExecutableReach(executable, chain) => reach::derive_executable_reach(world, executable, *chain),
        Job::DeriveInputDemand(function_id) => keying::derive_input_demand(world, tel, *function_id),
        Job::SeedRoot(root_id) => root::seed_root(world, tel, *root_id),
        Job::SeedActivation(activation) => root::seed_activation(world, tel, activation),
        Job::AnalyzeActivation(activation) => semantic::analyze_activation(world, tel, activation),
        Job::DeriveExecutableFacts(executable) => executable_facts::derive_executable_facts(world, tel, executable),
        Job::DeriveCallableConstructionTarget(key) => callable_target::derive(world, key),
        Job::DeriveRuntimeDemand(executable) => runtime_demand::derive_runtime_demand_fact(world, tel, executable),
    }
}

/// A job whose ground is gone concludes without running its body: whatever it
/// published is withdrawn, and the reads it keeps wake it should the ground
/// return. It is retired, not run: no derivation and no read is charged to it.
fn retire_ungrounded<T: crate::telemetry::RawSpanTelemetry>(
    context: &mut ExecutionContext<'_, T>,
    job: &Job,
) -> Option<JobEffects> {
    let (ground, effects) = retire_orphan(context.world, job).or_else(|| retire_unclaimed(context.world, job))?;
    context.emit_job_retired(&JobRetirement {
        job: job.clone(),
        ground,
    });
    Some(JobEffects {
        retired: true,
        ..effects
    })
}

/// A job on an orphaned generated function: the read of the owner's lowering
/// wakes it should the owner mint the lambda again.
fn retire_orphan(world: &mut World, job: &Job) -> Option<(RetirementGround, JobEffects)> {
    let function = job.subject_function().filter(|function| world.is_orphaned(*function))?;
    let owner = world.generated_owner(function)?;
    if let Job::AnalyzeActivation(activation) = job {
        world.clear_activation(activation);
    }
    Some((
        RetirementGround::OrphanedLambda { function, owner },
        JobEffects {
            reads: current_uses([FactKey::LoweredBody(owner)]),
            ..JobEffects::default()
        },
    ))
}

/// An activation analysis no caller claims: the read of its `Activation`
/// wakes it on a first or later claim.
fn retire_unclaimed(world: &World, job: &Job) -> Option<(RetirementGround, JobEffects)> {
    let Job::AnalyzeActivation(activation) = job else {
        return None;
    };
    let effects = semantic::retire_unclaimed(world, activation)?;
    Some((RetirementGround::UnclaimedActivation, effects))
}

impl Job {
    /// The function this job is about, for the kinds whose subject is one.
    pub(crate) fn subject_function(&self) -> Option<super::FunctionId> {
        match self {
            Job::ExpandFunctionSource(function)
            | Job::DefineFunction(function)
            | Job::DeriveFunctionContract(function)
            | Job::LowerFunction(function)
            | Job::ReifyGuardDispatch(function)
            | Job::PlanEntryDispatch(function)
            | Job::DeriveStaticCallees(function)
            | Job::DeriveRecursive(function)
            | Job::DeriveStaticReach(function)
            | Job::DeriveInputDemand(function) => Some(*function),
            Job::SeedActivation(activation) | Job::AnalyzeActivation(activation) => Some(activation.function),
            Job::DeriveExecutableReach(executable, _)
            | Job::DeriveExecutableFacts(executable)
            | Job::DeriveRuntimeDemand(executable) => Some(executable.activation.function),
            _ => None,
        }
    }

    /// The facts this job cannot conclude without, given its subject and the
    /// facts already present, each carrying the readiness it must be present
    /// at. Empty means every gate is satisfied, or this kind declares none.
    ///
    /// The scheduler calls this before handing out ANY popped job
    /// (`World::pop_runnable`) and before ever starting a never-run job by
    /// name (`World::demand_producer_if_needed`), and parks on each missing
    /// gate instead of starting the job to discover the same fact missing
    /// from inside its body. A job kind absent from the match below has no
    /// gate: it starts the moment anything demands its output, exactly as
    /// before this method existed.
    ///
    /// A wait a job's body discovers only while it runs -- a callee reached
    /// by walking a graph, a macro found mid-expansion -- is never a gate: a
    /// gate is nameable from the subject alone, before the job has read
    /// anything. `DeriveRuntimeDemand` and `DeriveExecutableFacts` gate on a
    /// settled answer, since both read their gate's value rather than merely
    /// its presence; every other kind gates on current.
    pub(crate) fn missing_gates(&self, world: &mut World) -> Vec<FactUse<FactKey>> {
        if self
            .subject_function()
            .is_some_and(|function| world.is_orphaned(function))
        {
            return Vec::new();
        }
        match self {
            Job::SeedRoot(root_id) => current_uses(root::seed_root_gates(world, *root_id)),
            Job::DefineFunction(function_id) => current_uses(source::define_function_gates(world, *function_id)),
            Job::ExpandFunctionSource(function_id) => {
                current_uses(source::expand_function_source_gates(world, *function_id))
            }
            Job::ScopeCode(source_owner) => current_uses(source::scope_code_gates(world, *source_owner)),
            Job::CheckDeclarations(source_owner) => {
                current_uses(declarations::check_declarations_gates(world, *source_owner))
            }
            Job::DeriveInputDemand(function_id) => current_uses(keying::derive_input_demand_gates(world, *function_id)),
            Job::DeriveRecursive(function_id) => current_uses(keying::derive_recursive_gates(world, *function_id)),
            Job::DeriveStaticReach(function_id) => current_uses(reach::derive_static_reach_gates(world, *function_id)),
            Job::DeriveExecutableReach(executable, _) => {
                settled_uses(reach::derive_executable_reach_gates(world, executable))
            }
            Job::DeriveRuntimeDemand(executable) => {
                settled_uses(runtime_demand::derive_runtime_demand_gates(world, executable))
            }
            Job::LowerFunction(function_id) => current_uses(body::lower_function_gates(world, *function_id)),
            Job::DeriveFunctionContract(function_id) => current_uses(
                world
                    .function_defined_revision(*function_id)
                    .is_none()
                    .then_some(FactKey::FunctionDefined(*function_id)),
            ),
            Job::DeriveStaticCallees(function_id) => {
                current_uses(keying::derive_static_callees_gates(world, *function_id))
            }
            Job::AnalyzeActivation(activation) => current_uses(semantic::analyze_activation_gates(world, activation)),
            Job::DefineModule(module_id) => current_uses(source::define_module_gates(world, *module_id)),
            Job::IndexCode(_)
            | Job::DefineModuleInterface(_)
            | Job::DeriveTypeDef(_)
            | Job::ReifyGuardDispatch(_)
            | Job::PlanEntryDispatch(_)
            | Job::SeedActivation(_)
            | Job::DeriveCallableConstructionTarget(_) => Vec::new(),
            Job::DeriveExecutableFacts(executable) => {
                settled_uses(executable_facts::derive_executable_facts_gates(world, executable))
            }
        }
    }
}
