use crate::ast::Program;
use crate::diag::{Diagnostics, SourceMap};
use crate::frontend::{FrontendOk, FrontendResult, compile_program_with_types, compile_source_with_types};
use crate::fz_ir::Module;
use crate::ir_codegen::AbiFacts;
use crate::ir_codegen::driver::prepare_preplanned_native;
use crate::ir_codegen::{
    AotArtifact, AotBackend, Backend, CodegenError, CompiledModule, CompiledUnit, JitBackend,
    compile_with_backend_prepared,
};
use crate::ir_planner::ModulePlan;
use crate::ir_planner::planned::PlannedProgram;
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
    units: Vec<CompiledUnit>,
    module: Option<Module>,
    module_plan: Option<ModulePlan>,
    sm: SourceMap,
    diagnostics: Diagnostics,
    working: Option<Module>,
    working_module_plan: Option<ModulePlan>,
    planned_program: Option<PlannedProgram>,
    abi_facts: Option<AbiFacts>,
}

impl World {
    pub(crate) fn new() -> Self {
        Self {
            types: types::new(),
            units: Vec::new(),
            module: None,
            module_plan: None,
            sm: SourceMap::new(),
            diagnostics: Diagnostics::new(),
            working: None,
            working_module_plan: None,
            planned_program: None,
            abi_facts: None,
        }
    }

    pub(crate) fn types(&mut self) -> &mut DefaultTypes {
        &mut self.types
    }

    pub(crate) fn units(&self) -> &[CompiledUnit] {
        &self.units
    }

    pub(crate) fn module(&self) -> &Module {
        self.module
            .as_ref()
            .expect("compiler world has no execution state; prepare the world before consuming it")
    }

    pub(crate) fn module_plan(&self) -> &ModulePlan {
        self.module_plan
            .as_ref()
            .expect("compiler world has no execution state; prepare the world before consuming it")
    }

    #[cfg(test)]
    pub(crate) fn cloned_module_plan(&self) -> (Module, ModulePlan) {
        (self.module().clone(), self.module_plan().clone())
    }

    pub(crate) fn sm(&self) -> &SourceMap {
        &self.sm
    }

    pub(crate) fn diagnostics(&self) -> &Diagnostics {
        &self.diagnostics
    }

    fn replace_execution(&mut self, graph: PreparedExecutionGraph) {
        self.units = graph.units;
        self.module = Some(graph.module);
        self.module_plan = Some(graph.module_plan);
        self.sm = graph.sm;
        self.diagnostics = graph.diagnostics;
        self.working = None;
        self.working_module_plan = None;
        self.planned_program = None;
        self.abi_facts = None;
    }

    fn replace_native(
        &mut self,
        working: Module,
        working_module_plan: ModulePlan,
        planned_program: PlannedProgram,
        abi_facts: AbiFacts,
    ) {
        self.working = Some(working);
        self.working_module_plan = Some(working_module_plan);
        self.planned_program = Some(planned_program);
        self.abi_facts = Some(abi_facts);
    }

    fn types_and_native(&mut self) -> (&mut DefaultTypes, &Module, &ModulePlan, &PlannedProgram, &AbiFacts) {
        let working = self
            .working
            .as_ref()
            .expect("compiler world has no native state; prepare native world state before codegen");
        let working_module_plan = self
            .working_module_plan
            .as_ref()
            .expect("compiler world has no native state; prepare native world state before codegen");
        let planned_program = self
            .planned_program
            .as_ref()
            .expect("compiler world has no native state; prepare native world state before codegen");
        let abi_facts = self
            .abi_facts
            .as_ref()
            .expect("compiler world has no native state; prepare native world state before codegen");
        (
            &mut self.types,
            working,
            working_module_plan,
            planned_program,
            abi_facts,
        )
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
        if world.working.is_some() {
            return Ok(());
        }
        let module = world.module().clone();
        let module_plan = world.module_plan().clone();
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

        let module_path = world.module().module_path().to_owned();
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

#[cfg(test)]
#[path = "compiler_test.rs"]
mod compiler_test;
