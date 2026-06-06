use crate::ast::Program;
use crate::diag::{Diagnostics, SourceMap};
use crate::frontend::{FrontendOk, FrontendResult, compile_program_with_types, compile_source_with_types};
use crate::fz_ir::Module;
use crate::ir_codegen::{
    AotArtifact, AotBackend, Backend, CodegenError, CompiledModule, CompiledUnit, JitBackend, PreparedNativeProgram,
    compile_with_backend_prepared, prepare_native_program,
};
use crate::ir_planner::ModulePlan;
use crate::metadata;
use crate::modules::pipeline::{
    CompileMode, PipelineError, PreparedExecutionGraph, checked_module_for_mode,
    prepare_execution_graph as build_execution_graph,
};
use crate::telemetry::{Telemetry, next_compile_nonce};
use crate::types;
use crate::types::DefaultTypes;

pub(crate) struct World {
    types: DefaultTypes,
    execution: Option<ExecutionWorld>,
    native: Option<PreparedNativeProgram>,
}

struct ExecutionWorld {
    units: Vec<CompiledUnit>,
    module: Module,
    module_plan: ModulePlan,
    sm: SourceMap,
    diagnostics: Diagnostics,
}

impl From<PreparedExecutionGraph> for ExecutionWorld {
    fn from(graph: PreparedExecutionGraph) -> Self {
        Self {
            units: graph.units,
            module: graph.module,
            module_plan: graph.module_plan,
            sm: graph.sm,
            diagnostics: graph.diagnostics,
        }
    }
}

impl World {
    pub(crate) fn new() -> Self {
        Self {
            types: types::new(),
            execution: None,
            native: None,
        }
    }

    pub(crate) fn types(&mut self) -> &mut DefaultTypes {
        &mut self.types
    }

    pub(crate) fn units(&self) -> &[CompiledUnit] {
        &self.execution().units
    }

    pub(crate) fn module(&self) -> &Module {
        &self.execution().module
    }

    pub(crate) fn module_plan(&self) -> &ModulePlan {
        &self.execution().module_plan
    }

    #[cfg(test)]
    pub(crate) fn cloned_module_plan(&self) -> (Module, ModulePlan) {
        (self.module().clone(), self.module_plan().clone())
    }

    pub(crate) fn sm(&self) -> &SourceMap {
        &self.execution().sm
    }

    pub(crate) fn diagnostics(&self) -> &Diagnostics {
        &self.execution().diagnostics
    }

    fn replace_execution(&mut self, graph: PreparedExecutionGraph) {
        self.execution = Some(graph.into());
        self.native = None;
    }

    fn replace_native(&mut self, prepared: PreparedNativeProgram) {
        self.native = Some(prepared);
    }

    fn types_and_native(&mut self) -> (&mut DefaultTypes, &PreparedNativeProgram) {
        let native = self
            .native
            .as_ref()
            .expect("compiler world has no native state; prepare native world state before codegen");
        (&mut self.types, native)
    }

    fn execution(&self) -> &ExecutionWorld {
        self.execution
            .as_ref()
            .expect("compiler world has no execution state; prepare the world before consuming it")
    }
}

pub(crate) struct Compiler;

impl Compiler {
    pub(crate) fn new() -> Self {
        Self
    }

    pub(crate) fn compile_source(
        &mut self,
        world: &mut World,
        src: String,
        source_name: String,
        tel: &dyn Telemetry,
    ) -> FrontendResult {
        compile_source_with_types(world.types(), src, source_name, tel)
    }

    pub(crate) fn compile_program(
        &mut self,
        world: &mut World,
        prog: Program,
        sm: SourceMap,
        tel: &dyn Telemetry,
    ) -> FrontendResult {
        compile_program_with_types(world.types(), prog, sm, tel)
    }

    pub(crate) fn prepare_execution_graph_from_source(
        &mut self,
        world: &mut World,
        src: String,
        source_name: String,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<(), PipelineError> {
        let frontend = self.compile_source(world, src, source_name, tel);
        self.prepare_execution_graph(world, frontend, tel, mode)
    }

    #[cfg(test)]
    pub(crate) fn prepare_execution_graph_from_program(
        &mut self,
        world: &mut World,
        prog: Program,
        sm: SourceMap,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<(), PipelineError> {
        let frontend = self.compile_program(world, prog, sm, tel);
        self.prepare_execution_graph(world, frontend, tel, mode)
    }

    pub(crate) fn prepare_execution_graph_from_frontend(
        &mut self,
        world: &mut World,
        frontend: FrontendOk,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<(), PipelineError> {
        self.prepare_execution_graph(world, Ok(frontend), tel, mode)
    }

    pub(crate) fn prepare_execution_graph(
        &mut self,
        world: &mut World,
        frontend: FrontendResult,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<(), PipelineError> {
        let checked = checked_module_for_mode(world.types(), frontend, tel, mode)?;
        let graph = build_execution_graph(world.types(), checked, tel, mode)?;
        world.replace_execution(graph);
        Ok(())
    }

    pub(crate) fn prepare_native_program(
        &mut self,
        world: &mut World,
        tel: &dyn Telemetry,
    ) -> Result<(), CodegenError> {
        if world.native.is_some() {
            return Ok(());
        }
        let module = world.module().clone();
        let module_plan = world.module_plan().clone();
        let prepared = prepare_native_program(world.types(), &module, &module_plan, tel)?;
        world.replace_native(prepared);
        Ok(())
    }

    pub(crate) fn compile_planned(
        &mut self,
        world: &mut World,
        tel: &dyn Telemetry,
    ) -> Result<CompiledModule, CodegenError> {
        self.compile_with_backend(world, JitBackend::new(), tel)
    }

    pub(crate) fn compile_aot_planned(
        &mut self,
        world: &mut World,
        obj_name: &str,
        tel: &dyn Telemetry,
    ) -> Result<AotArtifact, CodegenError> {
        self.compile_with_backend(world, AotBackend::new(obj_name), tel)
    }

    fn compile_with_backend<B: Backend>(
        &mut self,
        world: &mut World,
        backend: B,
        tel: &dyn Telemetry,
    ) -> Result<B::Output, CodegenError> {
        use crate::telemetry::TelemetryExt as _;

        let module_path = world.module().module_path().to_owned();
        let _compile_span = tel.span(
            &["fz", "compile"],
            metadata! {
                compile_nonce: next_compile_nonce(),
                module_path: module_path,
            },
        );
        self.prepare_native_program(world, tel)?;
        let (types, prepared) = world.types_and_native();
        compile_with_backend_prepared(types, prepared, backend, tel)
    }
}

#[cfg(test)]
#[path = "compiler_test.rs"]
mod compiler_test;
