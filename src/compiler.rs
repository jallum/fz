use crate::ast::Program;
use crate::diag::SourceMap;
use crate::frontend::{FrontendOk, FrontendResult, compile_program_with_types, compile_source_with_types};
use crate::ir_codegen::{
    AotArtifact, AotBackend, Backend, CodegenError, CompiledModule, JitBackend, PreparedNativeProgram,
    compile_with_backend_prepared, prepare_native_program,
};
use crate::metadata;
use crate::modules::pipeline::{
    CompileMode, PipelineError, PreparedExecutionGraph, checked_module_for_mode,
    prepare_execution_graph as build_execution_graph,
};
use crate::telemetry::{Telemetry, next_compile_nonce};
use crate::types;
use crate::types::DefaultTypes;

pub(crate) struct Compiler {
    types: DefaultTypes,
}

impl Compiler {
    pub(crate) fn new() -> Self {
        Self { types: types::new() }
    }

    pub(crate) fn with_types(types: DefaultTypes) -> Self {
        Self { types }
    }

    pub(crate) fn compile_source(&mut self, src: String, source_name: String, tel: &dyn Telemetry) -> FrontendResult {
        compile_source_with_types(self.types(), src, source_name, tel)
    }

    pub(crate) fn compile_program(&mut self, prog: Program, sm: SourceMap, tel: &dyn Telemetry) -> FrontendResult {
        compile_program_with_types(self.types(), prog, sm, tel)
    }

    pub(crate) fn prepare_execution_graph_from_source(
        &mut self,
        src: String,
        source_name: String,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<PreparedExecutionGraph, PipelineError> {
        let frontend = self.compile_source(src, source_name, tel);
        self.prepare_execution_graph(frontend, tel, mode)
    }

    pub(crate) fn prepare_execution_graph_from_program(
        &mut self,
        prog: Program,
        sm: SourceMap,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<PreparedExecutionGraph, PipelineError> {
        let frontend = self.compile_program(prog, sm, tel);
        self.prepare_execution_graph(frontend, tel, mode)
    }

    pub(crate) fn prepare_execution_graph_from_frontend(
        &mut self,
        frontend: FrontendOk,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<PreparedExecutionGraph, PipelineError> {
        self.prepare_execution_graph(Ok(frontend), tel, mode)
    }

    pub(crate) fn prepare_execution_graph(
        &mut self,
        frontend: FrontendResult,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<PreparedExecutionGraph, PipelineError> {
        let checked = checked_module_for_mode(self.types(), frontend, tel, mode)?;
        build_execution_graph(self.types(), checked, tel, mode)
    }

    pub(crate) fn prepare_native_program(
        &mut self,
        module: &crate::fz_ir::Module,
        module_plan: &crate::ir_planner::ModulePlan,
        tel: &dyn Telemetry,
    ) -> Result<PreparedNativeProgram, CodegenError> {
        prepare_native_program(self.types(), module, module_plan, tel)
    }

    pub(crate) fn compile_planned(
        &mut self,
        module: &crate::fz_ir::Module,
        module_plan: &crate::ir_planner::ModulePlan,
        tel: &dyn Telemetry,
    ) -> Result<CompiledModule, CodegenError> {
        self.compile_with_backend(module, module_plan, JitBackend::new(), tel)
    }

    pub(crate) fn compile_aot_planned(
        &mut self,
        module: &crate::fz_ir::Module,
        module_plan: &crate::ir_planner::ModulePlan,
        obj_name: &str,
        tel: &dyn Telemetry,
    ) -> Result<AotArtifact, CodegenError> {
        self.compile_with_backend(module, module_plan, AotBackend::new(obj_name), tel)
    }

    pub(crate) fn types(&mut self) -> &mut DefaultTypes {
        &mut self.types
    }

    pub(crate) fn into_types(self) -> DefaultTypes {
        self.types
    }

    fn compile_with_backend<B: Backend>(
        &mut self,
        module: &crate::fz_ir::Module,
        module_plan: &crate::ir_planner::ModulePlan,
        backend: B,
        tel: &dyn Telemetry,
    ) -> Result<B::Output, CodegenError> {
        use crate::telemetry::TelemetryExt as _;

        let _compile_span = tel.span(
            &["fz", "compile"],
            metadata! {
                compile_nonce: next_compile_nonce(),
                module_path: module.module_path().to_owned(),
            },
        );
        let prepared = self.prepare_native_program(module, module_plan, tel)?;
        compile_with_backend_prepared(self.types(), prepared, backend, tel)
    }
}

#[cfg(test)]
#[path = "compiler_test.rs"]
mod compiler_test;
