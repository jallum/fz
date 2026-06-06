use crate::compiler::source::SourceMap;
use crate::diag::Diagnostics;
use crate::fz_ir::Module;
use crate::ir_codegen::{AbiFacts, CompiledUnit};
use crate::ir_planner::ModulePlan;
use crate::ir_planner::planned::PlannedProgram;
use crate::modules::pipeline::PreparedExecutionGraph;
use crate::types;
use crate::types::DefaultTypes;

pub(crate) struct World {
    types: DefaultTypes,
    units: Vec<CompiledUnit>,
    linked_module: Option<Module>,
    linked_module_plan: Option<ModulePlan>,
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
            linked_module: None,
            linked_module_plan: None,
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

    pub(crate) fn linked_module(&self) -> &Module {
        self.linked_module
            .as_ref()
            .expect("compiler world has no execution state; prepare the world before consuming it")
    }

    pub(crate) fn linked_module_plan(&self) -> &ModulePlan {
        self.linked_module_plan
            .as_ref()
            .expect("compiler world has no execution state; prepare the world before consuming it")
    }

    #[cfg(test)]
    pub(crate) fn cloned_linked_module_plan(&self) -> (Module, ModulePlan) {
        (self.linked_module().clone(), self.linked_module_plan().clone())
    }

    pub(crate) fn sm(&self) -> &SourceMap {
        &self.sm
    }

    pub(crate) fn diagnostics(&self) -> &Diagnostics {
        &self.diagnostics
    }

    pub(super) fn has_native_program(&self) -> bool {
        self.working.is_some()
    }

    pub(super) fn replace_execution(&mut self, graph: PreparedExecutionGraph) {
        self.units = graph.units;
        self.linked_module = Some(graph.module);
        self.linked_module_plan = Some(graph.module_plan);
        self.sm = graph.sm;
        self.diagnostics = graph.diagnostics;
        self.working = None;
        self.working_module_plan = None;
        self.planned_program = None;
        self.abi_facts = None;
    }

    pub(super) fn replace_native(
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

    pub(super) fn types_and_native(&mut self) -> (&mut DefaultTypes, &Module, &ModulePlan, &PlannedProgram, &AbiFacts) {
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
