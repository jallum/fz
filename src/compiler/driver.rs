use super::World;
use crate::ast::Program;
use crate::compiler::source::SourceMap;
use crate::frontend::{FrontendOk, FrontendResult, compile_program_with_types, compile_source_with_types};
use crate::ir_codegen::driver::prepare_preplanned_native;
use crate::ir_codegen::{
    AotArtifact, AotBackend, Backend, CodegenError, CompiledModule, JitBackend, compile_with_backend_prepared,
};
use crate::metadata;
use crate::modules::pipeline::{
    CompileMode, PipelineError, checked_module_for_mode, prepare_execution_graph as build_execution_graph,
};
use crate::telemetry::{Telemetry, next_compile_nonce};

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
        if world.has_native_program() {
            return Ok(());
        }
        let module = world.linked_module().clone();
        let module_plan = world.linked_module_plan().clone();
        let (working, working_module_plan, planned_program, abi_facts) =
            prepare_preplanned_native(world.types(), &module, &module_plan, tel)?;
        world.replace_native(working, working_module_plan, planned_program, abi_facts);
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

        let module_path = world.linked_module().module_path().to_owned();
        let _compile_span = tel.span(
            &["fz", "compile"],
            metadata! {
                compile_nonce: next_compile_nonce(),
                module_path: module_path,
            },
        );
        self.prepare_native_program(world, tel)?;
        let (types, working, working_module_plan, planned_program, abi_facts) = world.types_and_native();
        compile_with_backend_prepared(
            types,
            working,
            working_module_plan,
            planned_program,
            abi_facts,
            backend,
            tel,
        )
    }
}
