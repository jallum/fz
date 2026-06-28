use crate::telemetry::{Telemetry, TelemetryExt as _, opaque_debug};
use crate::{measurements, metadata};
use std::time::Duration;

use super::NativeProgram;
use super::artifact::BackendProgram;
use super::code::CodeId;
use super::dump::DumpStage;
use super::facts::{FactReadiness, FactUse};
use super::identity::{FunctionId, RootId};
use super::pull::{ProductDriver, ProductKey, ProductValue, PullOutcome, PullWait, WorldProductProducers};
use super::scheduler::DriveOutcome;
use super::world::World;
use super::{ExecutableNeed, ModuleId, ModuleInterface};
use super::{FactKey, Job};

/// Public front door for the side-by-side incremental compiler.
///
/// Code enters Compiler2 as compiler-owned source text, receives stable
/// identity immediately, and can then seed root-scoped semantic work without
/// invoking the legacy lowering or planner pipeline.
pub struct Compiler2<'a> {
    tel: &'a dyn Telemetry,
    world: World<'a>,
    drive_timeout: Option<Duration>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CodeSubmission {
    pub name: Option<String>,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RootSubmission {
    pub module_name: Option<String>,
    pub name: String,
    pub arity: usize,
    pub need: ExecutableNeed,
}

impl<'a> Compiler2<'a> {
    pub fn new(tel: &'a dyn Telemetry) -> Self {
        Self {
            tel,
            world: World::new(tel),
            drive_timeout: None,
        }
    }

    pub fn set_drive_timeout(&mut self, timeout: Duration) {
        self.drive_timeout = Some(timeout);
    }

    pub fn submit_code(&mut self, submission: CodeSubmission) -> CodeId {
        let CodeSubmission { name, text } = submission;
        self.world.submit_code(name, text)
    }

    pub fn submit_module_interface(&mut self, module_name: String, interface: ModuleInterface) -> ModuleId {
        self.world.submit_module_interface(module_name, interface)
    }

    /// Submits one root request and seeds whatever source-surface work it needs.
    pub fn submit_root(&mut self, submission: RootSubmission) -> RootId {
        let RootSubmission {
            module_name,
            name,
            arity,
            need,
        } = submission;
        self.world.submit_root(module_name, name, arity, need)
    }

    /// Returns the entry `FunctionId` for the given root.
    pub fn root_function(&self, root: RootId) -> FunctionId {
        self.world.root_function(root)
    }

    pub fn demand(&mut self, job: Job) -> bool {
        self.world.demand(job)
    }

    pub fn drive(&mut self) -> DriveOutcome<Job, super::FactKey> {
        self.world.drive_for(self.drive_timeout)
    }

    fn native_program_for_root(&mut self, root: RootId) -> Result<NativeProgram, String> {
        self.drive_root_to(root, Job::LowerNativeProgram(root))?;
        Ok(self.world.native_program(root))
    }

    fn compile_native_backend<B>(
        &mut self,
        root: RootId,
        program: &NativeProgram,
        backend: B,
    ) -> Result<B::Output, super::native_codegen::CodegenError>
    where
        B: super::native_codegen::Backend,
    {
        let backend_kind = backend.kind();
        let tel = self.world.tel();
        let _span = tel.span(
            &["fz", "compiler2", "native_backend", "compile"],
            crate::metadata! {
                root_id: root.as_u32() as u64,
                backend_revision: program.backend_revision,
                entry_fn_id: program.entry.0 as u64,
                body_count: program.bodies.len() as u64,
                callable_boundary_count: program.callable_boundaries.len() as u64,
                backend: backend_kind,
            },
        );
        super::native_codegen::compile_with_backend_native_program(self.world.types_mut(), program, backend, tel)
    }

    fn drive_root_to(&mut self, root: RootId, job: Job) -> Result<(), String> {
        self.world.demand(job);
        match self.world.drive_for(self.drive_timeout) {
            DriveOutcome::Resolved => Ok(()),
            DriveOutcome::Unresolved { waits } => Err(format!(
                "compiler2 root {} stayed unresolved: {:?}",
                root.as_u32(),
                waits
            )),
            DriveOutcome::Fatal { job } => Err(format!(
                "compiler2 root {} failed before backend execution: {:?}",
                root.as_u32(),
                job
            )),
            DriveOutcome::TimedOut { jobs_ran, pending_jobs } => Err(format!(
                "compiler2 root {} exceeded {} ms drive limit after {} jobs with {} pending",
                root.as_u32(),
                self.drive_timeout
                    .expect("timed out drives should have a configured timeout")
                    .as_millis(),
                jobs_ran,
                pending_jobs,
            )),
        }
    }

    pub(crate) fn drive_root_to_dump_stage(&mut self, root: RootId, stage: DumpStage) -> Result<(), String> {
        match stage {
            DumpStage::Semantic => self.drive_root_to(root, Job::SealSemanticClosure(root)),
            DumpStage::Backend => self.product_backend_program_for_root(root).map(|_| ()),
            DumpStage::Native => self.drive_root_to(root, Job::LowerNativeProgram(root)),
        }
    }

    /// Drives one root to `BackendProgram` and runs it through the shared
    /// interpreter runtime without reopening the legacy planner pipeline.
    pub fn run_root_interp(&mut self, root: RootId) -> Result<i64, String> {
        let program = self.product_backend_program_for_root(root)?;
        let tel = self.world.tel();
        let (types, transport) = self.world.types_mut_and_transport();
        crate::ir_interp::run_backend_main(types, transport, tel, &program)
    }

    fn product_backend_program_for_root(&mut self, root: RootId) -> Result<BackendProgram, String> {
        if self.drive_timeout == Some(Duration::ZERO)
            && let DriveOutcome::TimedOut { jobs_ran, pending_jobs } = self.world.drive_for(self.drive_timeout)
        {
            return Err(format!(
                "compiler2 root {} exceeded 0 ms drive limit after {} jobs with {} pending",
                root.as_u32(),
                jobs_ran,
                pending_jobs,
            ));
        }
        let root_key = ProductKey::RootBackendProduct(root);
        let mut driver = ProductDriver::new(self.tel, root);
        let mut stack = vec![root_key.clone()];
        let mut last_wait = None;
        for _ in 0..50_000 {
            let Some(current) = stack.pop() else {
                stack.push(root_key.clone());
                continue;
            };
            let outcome = {
                let mut producers = WorldProductProducers::new(&mut self.world);
                driver.pull(&mut producers, current.clone())
            };
            match outcome {
                PullOutcome::Produced(ProductValue::RootBackendProduct(program)) if current == root_key => {
                    driver.finish_session();
                    return Ok(*program);
                }
                PullOutcome::Produced(_) => {}
                PullOutcome::Waiting(waits) => {
                    last_wait = Some((current.clone(), waits.clone()));
                    stack.push(current);
                    for wait in waits.into_iter().rev() {
                        match wait {
                            PullWait::Product(product) => stack.push(product),
                            PullWait::Fact(fact) => {
                                let producer_pokes = self.drive_product_fact_wait(root, fact)?;
                                driver.session_mut().record_producer_pokes(producer_pokes);
                            }
                        }
                    }
                }
            }
        }
        Err(format!(
            "compiler2 root {} product backend did not settle; last wait: {last_wait:?}",
            root.as_u32()
        ))
    }

    fn drive_product_fact_wait(&mut self, root: RootId, fact: FactUse<FactKey>) -> Result<u64, String> {
        let mut deferred = Vec::new();
        let mut jobs_ran = 0_u64;
        let mut producer_pokes = 0_u64;
        while !self.product_fact_wait_is_satisfied(&fact) {
            let job = match self.world.work_graph.pop() {
                Some(job) => job,
                None => {
                    producer_pokes += self.demand_product_fact_producer(fact.fact());
                    let Some(job) = self.world.work_graph.pop() else {
                        for job in deferred {
                            self.world.demand(job);
                        }
                        return Err(format!(
                            "compiler2 root {} product path waited on {:?} with no ready producer; unresolved={:?}",
                            root.as_u32(),
                            fact,
                            self.world.work_graph.unresolved()
                        ));
                    };
                    job
                }
            };
            if forbidden_product_path_job(root, &job) {
                deferred.push(job);
                continue;
            }
            let job_span = self.tel.span(
                &["fz", "compiler2", "job"],
                metadata! {
                    job: opaque_debug(&job),
                },
            );
            match super::jobs::run(&mut self.world, &job) {
                Ok(effects) => {
                    jobs_ran += 1;
                    job_span.stop_with(
                        &measurements! {},
                        &metadata! {
                            effects: opaque_debug(&effects),
                        },
                    );
                    self.world.complete_job(job, effects);
                }
                Err(_) => {
                    job_span.stop_with(&measurements! {}, &metadata! {});
                    for job in deferred {
                        self.world.demand(job);
                    }
                    return Err(format!(
                        "compiler2 root {} product path failed while producing {:?}: {:?}",
                        root.as_u32(),
                        fact,
                        job
                    ));
                }
            }
            if jobs_ran > 50_000 {
                for job in deferred {
                    self.world.demand(job);
                }
                return Err(format!(
                    "compiler2 root {} product path exceeded fact-wait budget for {:?}",
                    root.as_u32(),
                    fact
                ));
            }
        }
        Ok(producer_pokes)
    }

    fn demand_product_fact_producer(&mut self, fact: &FactKey) -> u64 {
        let job = match fact {
            FactKey::RootEntry(root) => Some(Job::SeedRoot(*root)),
            FactKey::FunctionDefined(function) => Some(Job::DefineFunction(*function)),
            FactKey::LoweredBody(function) => Some(Job::LowerFunction(*function)),
            FactKey::Recursive(function) => Some(Job::DeriveRecursive(*function)),
            FactKey::DispatchMask(function) => Some(Job::DeriveDispatchMask(*function)),
            FactKey::Activation(activation) | FactKey::ActivationInputs(activation) => {
                Some(Job::SeedActivation(activation.clone()))
            }
            FactKey::ActivationAnalyzed(activation) | FactKey::ReturnType(activation) => {
                let mut pokes = 0;
                if !self.world.has_fact(&FactKey::Activation(activation.clone()))
                    || !self.world.has_fact(&FactKey::ActivationInputs(activation.clone()))
                {
                    pokes += self.demand_if_needed(Job::SeedActivation(activation.clone()), fact) as u64;
                }
                return pokes + self.demand_if_needed(Job::AnalyzeActivation(activation.clone()), fact) as u64;
            }
            FactKey::CallSiteTargets(key) | FactKey::CallSiteSummary(key) => {
                let mut pokes = 0;
                if !self.world.has_fact(&FactKey::Activation(key.activation.clone()))
                    || !self.world.has_fact(&FactKey::ActivationInputs(key.activation.clone()))
                {
                    pokes += self.demand_if_needed(Job::SeedActivation(key.activation.clone()), fact) as u64;
                }
                return pokes + self.demand_if_needed(Job::AnalyzeActivation(key.activation.clone()), fact) as u64;
            }
            _ => None,
        };
        if let Some(job) = job {
            return self.demand_if_needed(job, fact) as u64;
        }
        0
    }

    fn demand_if_needed(&mut self, job: Job, target_fact: &FactKey) -> bool {
        if self.world.work_graph.output_keys(&job).contains(target_fact) && !self.world.work_graph.rebased(&job) {
            return false;
        }
        self.world.demand(job);
        true
    }

    fn product_fact_wait_is_satisfied(&self, fact: &FactUse<FactKey>) -> bool {
        match fact.readiness() {
            FactReadiness::Current => self.world.fact_revision(fact.fact()).is_some(),
            FactReadiness::Settled => self.world.fact_is_settled(fact.fact()),
        }
    }

    /// Drives one root to `NativeProgram` and JIT-compiles it through the
    /// shared native backend. The returned `FnId` is the root entry the
    /// runtime should spawn.
    pub fn compile_root_jit(
        &mut self,
        root: RootId,
    ) -> Result<(crate::ir_codegen::CompiledModule, crate::fz_ir::FnId), String> {
        let program = self.native_program_for_root(root)?;
        let entry = program.entry;
        let compiled = self
            .compile_native_backend(root, &program, super::native_codegen::JitBackend::new())
            .map_err(|err| format!("compiler2 root {} JIT compile failed: {err}", root.as_u32()))?;
        Ok((compiled, entry))
    }

    /// Drives one root to `NativeProgram`, JIT-compiles it, and runs the
    /// result through the shared runtime with the native module attached.
    pub fn run_root_jit(&mut self, root: RootId) -> Result<(), String> {
        let program = self.native_program_for_root(root)?;
        let compiled = self
            .compile_native_backend(root, &program, super::native_codegen::JitBackend::new())
            .map_err(|err| format!("compiler2 root {} JIT compile failed: {err}", root.as_u32()))?;
        let tel = self.world.tel();
        let mut runtime = crate::exec::runtime::Runtime::new(&compiled, 1, tel).with_module(&program.module);
        let _root_pid = runtime.spawn(program.entry);
        runtime.run_until_idle();
        Ok(())
    }

    /// Runs an executable macro over a quoted source heap and returns the
    /// macro-produced root in that same heap.
    pub fn run_macro_on_source(
        &mut self,
        function: super::FunctionId,
        source: &super::QuotedSourceRoot,
        caller: fz_runtime::any_value::AnyValueRef,
        args: &[fz_runtime::any_value::AnyValueRef],
    ) -> Result<super::QuotedSourceRoot, String> {
        self.world.run_macro_on_source(function, source, caller, args)
    }

    #[cfg(test)]
    pub(crate) fn compile_native_program_jit_for_test(
        &mut self,
        program: &NativeProgram,
    ) -> Result<crate::ir_codegen::CompiledModule, String> {
        let tel = self.world.tel();
        super::native_codegen::compile_with_backend_native_program(
            self.world.types_mut(),
            program,
            super::native_codegen::JitBackend::new(),
            tel,
        )
        .map_err(|err| format!("compiler2 native program JIT compile failed: {err}"))
    }

    #[cfg(test)]
    pub(crate) fn types_equivalent_for_test(&self, left: super::Ty, right: super::Ty) -> bool {
        self.world.types().is_equivalent(&left, &right)
    }

    #[cfg(test)]
    pub(crate) fn display_ty_for_test(&self, ty: super::Ty) -> String {
        self.world.types().display(&ty)
    }

    #[cfg(test)]
    pub(crate) fn types_mut_for_test(&mut self) -> &mut super::types::Types {
        self.world.types_mut()
    }

    #[cfg(test)]
    pub(crate) fn types_for_test(&self) -> &super::types::Types {
        self.world.types()
    }

    /// Drives one root to `NativeProgram` and emits an AOT object through the
    /// shared native backend.
    pub fn compile_root_aot(&mut self, root: RootId, obj_name: &str) -> Result<crate::ir_codegen::AotArtifact, String> {
        let program = self.native_program_for_root(root)?;
        self.compile_native_backend(root, &program, super::native_codegen::AotBackend::new(obj_name))
            .map_err(|err| format!("compiler2 root {} AOT compile failed: {err}", root.as_u32()))
    }
}

fn forbidden_product_path_job(root: RootId, job: &Job) -> bool {
    matches!(
        job,
        Job::SealSemanticClosure(candidate)
            | Job::DeriveTransportPlan(candidate)
            | Job::BuildBackendProduct(candidate)
            if *candidate == root
    )
}
