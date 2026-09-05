use crate::telemetry::{RawSpanTelemetry, Telemetry, TelemetryExt as _};
use std::rc::Rc;
use std::time::Duration;

use super::NativeProgram;
use super::artifact::BackendProgram;
use super::code::CodeId;
use super::drive::ExecutionContext;
use super::dump::DumpStage;
use super::facts::FactUse;
use super::identity::{ActivationKey, ExecutableKey, FunctionId, RootId};
use super::pull::{ProductKey, ProductSessions, PullWait};
use super::scheduler::DriveOutcome;
use super::world::World;
use super::{ExecutableNeed, ModuleId, ModuleInterface};
use super::{FactKey, Job};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BackendRequestEvent {
    Started,
    Succeeded {
        executables: usize,
        construction_wrappers: usize,
    },
    Failed,
}

/// Public front door for the side-by-side incremental compiler.
///
/// Code enters Compiler2 as compiler-owned source text, receives stable
/// identity immediately, and can then seed root-scoped semantic work without
/// invoking the legacy lowering or planner pipeline.
pub struct Compiler2<T: Telemetry> {
    world: World,
    telemetry: T,
    output: Box<dyn fz_runtime::output::OutputSink>,
    requested_output: Box<dyn super::dump::RequestedOutputSink>,
    drive_timeout: Option<Duration>,
    product_sessions: ProductSessions,
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

impl<T: RawSpanTelemetry> Compiler2<T> {
    pub fn new(telemetry: T) -> Self {
        Self {
            world: World::new(),
            telemetry,
            output: Box::new(fz_runtime::output::StdoutOutput),
            requested_output: Box::new(super::dump::NullRequestedOutput),
            drive_timeout: None,
            product_sessions: ProductSessions::default(),
        }
    }

    pub fn set_drive_timeout(&mut self, timeout: Duration) {
        self.drive_timeout = Some(timeout);
    }

    pub fn set_output(&mut self, output: Box<dyn fz_runtime::output::OutputSink>) {
        self.output = output;
    }

    pub(crate) fn set_requested_output(&mut self, output: Box<dyn super::dump::RequestedOutputSink>) {
        self.requested_output = output;
    }

    pub(crate) fn telemetry(&self) -> &T {
        &self.telemetry
    }

    pub(crate) fn source_map(&self) -> std::rc::Rc<std::cell::RefCell<crate::source::SourceMap>> {
        self.world.source_map()
    }

    pub fn submit_code(&mut self, submission: CodeSubmission) -> CodeId {
        let CodeSubmission { name, text } = submission;
        ExecutionContext::new(&mut self.world, &self.telemetry).submit_code(name, text)
    }

    /// Registers an additional user-surface prelude — ordinary source scoped in
    /// over the runtime prelude so its top-level definitions become visible to
    /// every later `submit_code`/`submit_root` in this compiler, with no text
    /// spliced into any user source buffer. Must be called before submitting the
    /// code that should see it. `fz2 test` uses this to make the `test` item
    /// macro available to a test file scoped into this run's world only.
    pub fn submit_scoped_prelude(&mut self, submission: CodeSubmission) -> CodeId {
        let CodeSubmission { name, text } = submission;
        self.world.register_scoped_prelude(name, text)
    }

    /// Registers another module's interface without handing this compiler
    /// that module's source: the front door for an embedder that owns a
    /// module out-of-band (a host-provided module, or a sibling compilation
    /// unit compiled elsewhere) and wants code submitted here to import
    /// against it. The module settles on the published interface alone —
    /// no body definition is required or implied.
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
        ExecutionContext::new(&mut self.world, &self.telemetry).submit_root(module_name, name, arity, need)
    }

    /// Returns the entry `FunctionId` for the given root.
    pub fn root_function(&self, root: RootId) -> FunctionId {
        self.world.root_function(root)
    }

    pub fn demand(&mut self, job: Job) -> bool {
        self.world.demand(job)
    }

    pub fn drive(&mut self) -> DriveOutcome<Job, super::DependencyKey> {
        self.product_sessions
            .begin_standalone_drive(self.world.work_start_tally());
        let outcome = super::drive::ExecutionContext::with_product_sessions(
            &mut self.world,
            &self.telemetry,
            &mut self.product_sessions,
        )
        .drive_for(self.drive_timeout);
        self.product_sessions
            .finish_standalone_drive(self.world.work_start_tally());
        outcome
    }

    fn native_program_for_root(&mut self, root: RootId) -> Result<Rc<NativeProgram>, String> {
        super::product_drive::drive_retained_root_native_program(
            &mut self.world,
            &self.telemetry,
            &mut self.product_sessions,
            root,
            self.drive_timeout,
        )
    }

    fn compile_native_backend<B>(
        &mut self,
        program: &NativeProgram,
        backend: B,
    ) -> Result<B::Output, super::native_codegen::CodegenError>
    where
        B: super::native_codegen::Backend,
    {
        let Self {
            world,
            telemetry,
            requested_output,
            ..
        } = self;
        let _span = telemetry.raw_span1_0(&["fz", "compiler2", "native_backend", "compile"], program);
        super::native_codegen::compile_with_backend_native_program(
            world.types_mut(),
            program,
            backend,
            telemetry,
            &mut **requested_output,
        )
    }

    pub(crate) fn drive_root_to_dump_stage(
        &mut self,
        root: RootId,
        stage: DumpStage,
    ) -> Result<(Rc<BackendProgram>, Option<Rc<NativeProgram>>), String> {
        match stage {
            DumpStage::Backend => self
                .product_backend_program_for_root(root)
                .map(|backend| (backend, None)),
            DumpStage::Native => {
                let native = self.native_program_for_root(root)?;
                let backend = match self
                    .product_sessions
                    .get(root)
                    .and_then(|session| session.memo().get(&ProductKey::RootBackendProduct(root)).cloned())
                {
                    Some(super::pull::ProductValue::RootBackendProduct(backend)) => backend,
                    _ => panic!("native product must retain its exact backend content dependency"),
                };
                Ok((backend, Some(native)))
            }
        }
    }

    /// Serves the `types`/`activations` CLI dumps from the product-path
    /// activation inventory.
    ///
    /// The product backend drive enumerates the executables it MATERIALIZES —
    /// the activations actually compiled into the program, analyzed through the
    /// world facts the dump reads. That set is exactly the fully-reached
    /// reachable closure (the demand frontier may briefly over-ask for
    /// dispatch-sibling activations that never materialize; those are not part
    /// of the program and must not appear in the dump). Walking the materialized
    /// inventory and emitting the per-activation dump events keeps the dump
    /// content sourced entirely from demanded products.
    pub(crate) fn emit_product_semantic_dumps(&mut self, root: RootId) -> Result<(), String> {
        let activations = self.product_activation_inventory(root)?;
        self.requested_output.semantic(&self.world, root, &activations);
        Ok(())
    }

    pub(crate) fn emit_requested_program_dumps(
        &mut self,
        root: RootId,
        backend: &BackendProgram,
        native: Option<&NativeProgram>,
    ) {
        self.requested_output.program(&self.world, root, backend, native);
    }

    /// Drives one root to its backend product and returns the settled
    /// product-path activation inventory: the activations the product actually
    /// materializes.
    ///
    /// The product drive discovers executables through runtime demand and
    /// callable flow, not just static callsites, so this set includes
    /// escaped/opaque callables — e.g. a generated lambda reached only through
    /// an `f.(x)` boundary. That is the frontier the CLI semantic dump reads,
    /// and the frontier fixture call-edge oracles source so latent
    /// runtime-demand-reached provenance is observable.
    pub(crate) fn product_activation_inventory(&mut self, root: RootId) -> Result<Vec<ActivationKey>, String> {
        let executables = self.product_executable_inventory(root)?;
        Ok(executables
            .into_iter()
            .map(|executable| executable.activation)
            .collect())
    }

    /// Drives one root to its backend product and returns the settled
    /// product-path executable inventory: the `ExecutableKey`s the product
    /// actually materializes (each an activation paired with its need). This is
    /// the executable-grained counterpart of `product_activation_inventory` —
    /// multiple executables can share one activation under different needs — and
    /// is the canonical source of the semantic executable/activation metrics the
    /// fixture contract harness asserts.
    pub(crate) fn product_executable_inventory(&mut self, root: RootId) -> Result<Vec<ExecutableKey>, String> {
        let program = self.drive_root_backend_product(root)?;
        let executables = program
            .executables()
            .iter()
            .map(|executable| executable.key.clone())
            .collect::<Vec<_>>();
        Ok(executables)
    }

    /// Drives one root to its backend product and returns the World's
    /// cumulative work-start attribution. The running pull-only guard
    /// (`work_start_reason_test`) asserts on this: `unsanctioned_work_starts()`,
    /// `root_scans`, and `drain_discovery_sweeps` must be zero, and `ignition`
    /// must equal the true external front-door count (one `submit_code` + one
    /// `submit_root`).
    #[cfg(test)]
    pub(crate) fn drive_root_backend_work_starts(&mut self, root: RootId) -> Result<super::WorkStartTally, String> {
        self.drive_root_backend_product(root)?;
        Ok(self.world.work_start_tally())
    }

    /// Read-only access to the compiler's settled world, so tests can read the
    /// facts a product drive published (activation analyses, callsite
    /// summaries) alongside the returned activation inventory.
    #[cfg(test)]
    pub(crate) fn world(&self) -> &World {
        &self.world
    }

    #[cfg(test)]
    pub(crate) fn world_mut(&mut self) -> &mut World {
        &mut self.world
    }

    /// Drives one root to `BackendProgram` and runs it through the shared
    /// interpreter runtime without reopening the legacy planner pipeline.
    pub fn run_root_interp(&mut self, root: RootId) -> Result<i64, String> {
        let program = self.product_backend_program_for_root(root)?;
        let tel = &self.telemetry;
        let (types, transport) = self.world.types_mut_and_transport();
        crate::ir_interp::run_backend_main(types, transport, tel, self.output.as_ref(), &program)
    }

    fn product_backend_program_for_root(&mut self, root: RootId) -> Result<Rc<BackendProgram>, String> {
        const STARTED: &[&str] = &["fz", "compiler2", "backend_request", "started"];
        const FINISHED: &[&str] = &["fz", "compiler2", "backend_request", "finished"];
        let emit_lifecycle =
            self.telemetry.is_raw_event_enabled(STARTED) || self.telemetry.is_raw_event_enabled(FINISHED);
        if emit_lifecycle {
            self.telemetry
                .raw_event3(STARTED, &self.world, &root, &BackendRequestEvent::Started);
        }
        let result = self.drive_root_backend_product(root);
        if emit_lifecycle {
            let event = match &result {
                Ok(program) => BackendRequestEvent::Succeeded {
                    executables: program.executables().len(),
                    construction_wrappers: program.construction_wrappers().len(),
                },
                Err(_) => BackendRequestEvent::Failed,
            };
            self.telemetry.raw_event3(FINISHED, &self.world, &root, &event);
        }
        result
    }

    /// Drives one root to its memo-owned, shared `BackendProgram`.
    fn drive_root_backend_product(&mut self, root: RootId) -> Result<Rc<BackendProgram>, String> {
        super::product_drive::drive_retained_root_backend_product(
            &mut self.world,
            &self.telemetry,
            &mut self.product_sessions,
            root,
            self.drive_timeout,
        )
    }

    /// Releases one root's retained product spreadsheet and every exact fact
    /// subscription that routes movements to it. Requesting the known root
    /// again begins a fresh product calculation over the same semantic World.
    pub fn retire_root_products(&mut self, root: RootId) -> bool {
        let changes = self.product_sessions.retirement_changes(root);
        let retired = self.product_sessions.retire(root, self.world.types());
        ExecutionContext::with_product_sessions(&mut self.world, &self.telemetry, &mut self.product_sessions)
            .apply_product_changes(changes);
        retired
    }

    #[cfg(test)]
    pub(crate) fn retained_product_counts(&self) -> (usize, usize) {
        self.product_sessions.counts()
    }

    #[cfg(test)]
    pub(crate) fn retained_backend_program(&self, root: RootId) -> Rc<BackendProgram> {
        match self
            .product_sessions
            .get(root)
            .and_then(|session| session.memo().get(&ProductKey::RootBackendProduct(root)).cloned())
        {
            Some(super::pull::ProductValue::RootBackendProduct(answer)) => Rc::clone(&answer),
            _ => panic!("root product must be retained after a successful request"),
        }
    }

    #[cfg(test)]
    pub(crate) fn retained_native_program(&self, root: RootId) -> Rc<NativeProgram> {
        match self
            .product_sessions
            .get(root)
            .and_then(|session| session.memo().get(&ProductKey::NativeProgram(root)).cloned())
        {
            Some(super::pull::ProductValue::NativeProgram(program)) => program,
            _ => panic!("native product must be retained after a successful request"),
        }
    }

    #[cfg(test)]
    pub(crate) fn retained_product_generation(&self, root: RootId, key: &ProductKey) -> Option<u64> {
        self.product_sessions.get(root)?.memo().generation(key)
    }

    #[cfg(test)]
    pub(crate) fn reproduce_job_for_test(&mut self, job: Job, changed: Vec<FactKey>) -> super::JobCompletion {
        let mut context =
            ExecutionContext::with_product_sessions(&mut self.world, &self.telemetry, &mut self.product_sessions);
        let mut effects =
            super::jobs::run(&mut context, &job).expect("test producer must reproduce its existing answer");
        effects.changed.extend(changed);
        context.complete_job(job, effects)
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
            .compile_native_backend(&program, super::native_codegen::JitBackend::new())
            .map_err(|err| format!("compiler2 root {} JIT compile failed: {err}", root.as_u32()))?;
        Ok((compiled, entry))
    }

    /// Drives one root to `NativeProgram`, JIT-compiles it, and runs the
    /// result through the shared runtime with the native module attached.
    pub fn run_root_jit(&mut self, root: RootId) -> Result<(), String> {
        let program = self.native_program_for_root(root)?;
        let compiled = self
            .compile_native_backend(&program, super::native_codegen::JitBackend::new())
            .map_err(|err| format!("compiler2 root {} JIT compile failed: {err}", root.as_u32()))?;
        let tel = &self.telemetry;
        let mut runtime = crate::exec::runtime::Runtime::new(&compiled, 1, tel)
            .with_module(&program.module)
            .with_output(self.output.as_ref());
        let root_pid = runtime.spawn(program.entry);
        runtime.run_until_idle();
        // A fault-halted root must not report success (fz-bdk). The exit
        // kind is set by the fault trap itself; render the reason atom the
        // same way interp's abort names it.
        if let Some(atom) = runtime.exit_fault(root_pid) {
            let reason = program
                .module
                .atom_names
                .get(atom as usize)
                .map(String::as_str)
                .unwrap_or("unknown_fault");
            return Err(format!("{reason}: the root process halted through a fault trap"));
        }
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
        if self.world.function_defined_revision(function).is_none() {
            self.world.demand_fact_producer(
                &FactKey::FunctionDefined(function),
                super::scheduler::WorkStartReason::BlockedWaiterExpansion,
            );
            let outcome = self.drive();
            if !matches!(outcome, DriveOutcome::Resolved) || self.world.function_defined_revision(function).is_none() {
                return Err(format!(
                    "compiler2 macro {} could not resolve its definition: {outcome:?}",
                    function.as_u32()
                ));
            }
        }
        if !self.world.function_definition(function).1.is_macro {
            return Err(format!("compiler2 function {} is not a macro", function.as_u32()));
        }
        let root = self.world.macro_root(function);
        let program = self.product_backend_program_for_root(root)?;
        ExecutionContext::new(&mut self.world, &self.telemetry)
            .run_macro_on_source(function, &program, source, caller, args)
    }

    #[cfg(test)]
    pub(crate) fn compile_native_program_jit_for_test(
        &mut self,
        program: &NativeProgram,
    ) -> Result<crate::ir_codegen::CompiledModule, String> {
        let tel = &self.telemetry;
        super::native_codegen::compile_with_backend_native_program(
            self.world.types_mut(),
            program,
            super::native_codegen::JitBackend::new(),
            tel,
            &mut super::dump::NullRequestedOutput,
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
        self.compile_native_backend(&program, super::native_codegen::AotBackend::new(obj_name))
            .map_err(|err| format!("compiler2 root {} AOT compile failed: {err}", root.as_u32()))
    }
}

/// Reports `RootBackendProduct` pull-drive failures as plain `String`s for
/// the in-memory front door (`run_root_interp`, `product_executable_inventory`,
/// the CLI dump paths). Unlike the backend job's `FatalError` counterpart,
/// this path does not emit a diagnostic — it never has, and the drive-loop
/// unification is not the place to change that.
impl super::product_drive::ProductDriveError for String {
    fn dependency_failed<T: crate::telemetry::Telemetry>(
        _world: &World,
        _tel: &T,
        address: super::drive::ProductAddress,
        _source: super::scheduler::FatalError,
    ) -> Self {
        format!("compiler2 product dependency {address:?} failed")
    }
    fn product_failed<T: Telemetry>(
        _world: &World,
        _tel: &T,
        root: RootId,
        product: &ProductKey,
        _failure: super::pull::ProductFailure,
    ) -> Self {
        format!("compiler2 root {} failed producing {product:?}", root.as_u32())
    }

    fn job_failed<T: Telemetry>(
        _world: &World,
        _tel: &T,
        root: RootId,
        fact: &FactUse<FactKey>,
        job: &Job,
        _source: super::scheduler::FatalError,
    ) -> Self {
        format!(
            "compiler2 root {} product path failed while producing {:?}: {:?}",
            root.as_u32(),
            fact,
            job
        )
    }

    fn no_ready_producer<T: Telemetry>(world: &World, _tel: &T, root: RootId, fact: &FactUse<FactKey>) -> Self {
        format!(
            "compiler2 root {} product path waited on {:?} with no ready producer; unresolved={:?}",
            root.as_u32(),
            fact,
            world.unresolved_waits()
        )
    }

    fn fact_wait_budget_exceeded<T: Telemetry>(
        _world: &World,
        _tel: &T,
        root: RootId,
        fact: &FactUse<FactKey>,
    ) -> Self {
        format!(
            "compiler2 root {} product path exceeded fact-wait budget for {:?}",
            root.as_u32(),
            fact
        )
    }

    fn did_not_settle<T: Telemetry>(
        _world: &World,
        _tel: &T,
        root: RootId,
        last_wait: Option<(ProductKey, Vec<PullWait>)>,
    ) -> Self {
        format!(
            "compiler2 root {} product backend did not settle; last wait: {last_wait:?}",
            root.as_u32()
        )
    }
}
