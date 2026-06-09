use crate::telemetry::Telemetry;

use super::ExecutableNeed;
use super::Job;
use super::NativeProgram;
use super::code::CodeId;
use super::identity::RootId;
use super::scheduler::DriveOutcome;
use super::world::World;

/// Public front door for the side-by-side incremental compiler.
///
/// Code enters Compiler2 as compiler-owned source text, receives stable
/// identity immediately, and can then seed root-scoped semantic work without
/// invoking the legacy lowering or planner pipeline.
pub struct Compiler2<'a> {
    world: World<'a>,
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
        Self { world: World::new(tel) }
    }

    pub fn submit_code(&mut self, submission: CodeSubmission) -> CodeId {
        let CodeSubmission { name, text } = submission;
        self.world.submit_code(name, text)
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

    pub fn demand(&mut self, job: Job) -> bool {
        self.world.demand(job)
    }

    pub fn drive(&mut self) -> DriveOutcome<Job, super::FactKey> {
        self.world.drive()
    }

    fn native_program_for_root(&mut self, root: RootId) -> Result<NativeProgram, String> {
        self.drive_root_to(root, Job::LowerNativeProgram(root))?;
        Ok(self.world.native_program(root))
    }

    fn drive_root_to(&mut self, root: RootId, job: Job) -> Result<(), String> {
        self.world.demand(job);
        match self.world.drive() {
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
        let tel = self.world.tel();
        let compiled = super::native_codegen::compile_with_backend_native_program(
            self.world.types_mut(),
            &program,
            super::native_codegen::JitBackend::new(),
            tel,
        )
        .map_err(|err| format!("compiler2 root {} JIT compile failed: {err}", root.as_u32()))?;
        Ok((compiled, entry))
    }

    /// Drives one root to `NativeProgram`, JIT-compiles it, and runs the
    /// result through the shared runtime with the native module attached.
    pub fn run_root_jit(&mut self, root: RootId) -> Result<(), String> {
        let program = self.native_program_for_root(root)?;
        let tel = self.world.tel();
        let compiled = super::native_codegen::compile_with_backend_native_program(
            self.world.types_mut(),
            &program,
            super::native_codegen::JitBackend::new(),
            tel,
        )
        .map_err(|err| format!("compiler2 root {} JIT compile failed: {err}", root.as_u32()))?;
        let mut runtime = crate::exec::runtime::Runtime::new(&compiled, 1, tel).with_module(&program.module);
        let _root_pid = runtime.spawn(program.entry);
        runtime.run_until_idle();
        Ok(())
    }

    /// Drives one root to `NativeProgram` and emits an AOT object through the
    /// shared native backend.
    pub fn compile_root_aot(&mut self, root: RootId, obj_name: &str) -> Result<crate::ir_codegen::AotArtifact, String> {
        let program = self.native_program_for_root(root)?;
        let tel = self.world.tel();
        super::native_codegen::compile_with_backend_native_program(
            self.world.types_mut(),
            &program,
            super::native_codegen::AotBackend::new(obj_name),
            tel,
        )
        .map_err(|err| format!("compiler2 root {} AOT compile failed: {err}", root.as_u32()))
    }
}
