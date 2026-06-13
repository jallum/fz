use crate::telemetry::{Telemetry, TelemetryExt as _};
use std::time::Duration;

use super::Job;
use super::NativeProgram;
use super::code::CodeId;
use super::identity::{FunctionId, RootId};
use super::scheduler::DriveOutcome;
use super::world::World;
use super::{ExecutableNeed, ModuleId, ModuleInterface};

/// Public front door for the side-by-side incremental compiler.
///
/// Code enters Compiler2 as compiler-owned source text, receives stable
/// identity immediately, and can then seed root-scoped semantic work without
/// invoking the legacy lowering or planner pipeline.
pub struct Compiler2<'a> {
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
                callable_entry_count: program.callable_boundaries.len() as u64,
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

    /// Drives one root to `BackendProgram` and runs it through the shared
    /// interpreter runtime without reopening the legacy planner pipeline.
    pub fn run_root_interp(&mut self, root: RootId) -> Result<i64, String> {
        self.drive_root_to(root, Job::LowerBackendProgram(root))?;
        let program = self.world.backend_program(root);
        let tel = self.world.tel();
        crate::ir_interp::run_backend_main(self.world.types_mut(), tel, &program)
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

    /// Drives one root to `NativeProgram` and emits an AOT object through the
    /// shared native backend.
    pub fn compile_root_aot(&mut self, root: RootId, obj_name: &str) -> Result<crate::ir_codegen::AotArtifact, String> {
        let program = self.native_program_for_root(root)?;
        self.compile_native_backend(root, &program, super::native_codegen::AotBackend::new(obj_name))
            .map_err(|err| format!("compiler2 root {} AOT compile failed: {err}", root.as_u32()))
    }
}
