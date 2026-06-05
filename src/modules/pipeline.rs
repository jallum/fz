//! Module-aware frontend and execution-graph preparation.

use crate::compiler::{CompilerWorld, ModuleId, ModuleKey, RuntimeReachabilitySeed};
use crate::diag::codes::{CODEGEN_SCHEMA_MISSING, LOWER_UNBOUND};
use crate::diag::diagnostic::Severity;
use crate::diag::{Diagnostic, Diagnostics, SourceMap, Span, emit_through};
use crate::frontend::resolve::InterfaceTable;
use crate::frontend::{FrontendOk, FrontendResult};
use crate::fz_ir::Module;
use crate::ir_codegen::{CompiledUnit, ImageLinkError, link_ir_units};
use crate::ir_planner::fn_types::CallEdgeTarget;
use crate::ir_planner::{ModulePlan, plan_module};
use crate::metadata;
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{ModuleInterface, validate_public_export_specs};
use crate::telemetry::{Telemetry, next_compile_nonce};
use crate::types::DefaultTypes;
use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt::{Display, Formatter};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CompileMode {
    Normal,
    Lto,
}

impl CompileMode {
    pub(crate) fn is_lto(self) -> bool {
        matches!(self, Self::Lto)
    }
}

pub(crate) struct CheckedModule {
    pub(crate) module: Module,
    pub(crate) module_plan: ModulePlan,
    pub(crate) interfaces: BTreeMap<ModuleName, ModuleInterface>,
    pub(crate) external_interfaces: BTreeMap<ModuleName, ModuleInterface>,
    pub(crate) sm: SourceMap,
    pub(crate) diagnostics: Diagnostics,
}

impl CheckedModule {
    pub(crate) fn compiled_unit_input(&self) -> CompiledUnit {
        let interface = ModuleName::parse_dotted(self.module.module_path())
            .ok()
            .and_then(|module| self.interfaces.get(&module).cloned())
            .or_else(|| {
                if self.interfaces.len() == 1 {
                    self.interfaces.values().next().cloned()
                } else {
                    None
                }
            });
        CompiledUnit::from_ir_module_with_plan(
            self.module.clone(),
            Some(self.module_plan.clone()),
            interface,
            Diagnostics::new(),
        )
    }
}

pub(crate) struct PreparedExecutionGraph {
    pub(crate) units: Vec<CompiledUnit>,
    pub(crate) module: Module,
    pub(crate) module_plan: ModulePlan,
    pub(crate) sm: SourceMap,
}

pub(crate) struct LinkedExecutionModule {
    pub(crate) units: Vec<CompiledUnit>,
    pub(crate) module: Module,
}

#[derive(Debug)]
pub(crate) enum PipelineError {
    FrontendFailed,
    FrontendDiagnostics,
    LtoInterfaceSpecs,
    LtoRewriteFailed,
    Link(ImageLinkError),
}

impl Display for PipelineError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FrontendFailed => f.write_str("frontend failed"),
            Self::FrontendDiagnostics => f.write_str("frontend reported errors"),
            Self::LtoInterfaceSpecs => f.write_str("LTO interface validation failed"),
            Self::LtoRewriteFailed => f.write_str("LTO rewrite failed"),
            Self::Link(err) => write!(f, "{err}"),
        }
    }
}

impl Error for PipelineError {}

impl PipelineError {
    pub(crate) fn diagnostics_emitted(&self) -> bool {
        match self {
            Self::FrontendFailed | Self::FrontendDiagnostics | Self::LtoInterfaceSpecs | Self::LtoRewriteFailed => true,
            Self::Link(_) => false,
        }
    }
}

pub(crate) fn link_error_diagnostic(err: ImageLinkError) -> Diagnostic {
    Diagnostic::error(CODEGEN_SCHEMA_MISSING, err.to_string(), Span::DUMMY)
}

fn run_frontend(result: FrontendResult, tel: &dyn Telemetry) -> Result<FrontendOk, PipelineError> {
    let ok = match result {
        Ok(ok) => ok,
        Err(err) => {
            emit_through(tel, Some(&err.sm), err.diagnostics.as_slice());
            return Err(PipelineError::FrontendFailed);
        }
    };
    if has_errors(&ok.diagnostics) {
        emit_through(tel, Some(&ok.sm), ok.diagnostics.as_slice());
        return Err(PipelineError::FrontendDiagnostics);
    }
    Ok(ok)
}

fn has_errors(diagnostics: &Diagnostics) -> bool {
    diagnostics
        .as_slice()
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
}

fn planned_external_targets(module_plan: &ModulePlan) -> BTreeSet<ExportKey> {
    let mut targets = BTreeSet::new();
    for spec_key in &module_plan.reachable_specs {
        let Some(spec) = module_plan.specs.get(spec_key) else {
            continue;
        };
        for edge in spec.call_edges.values() {
            if let CallEdgeTarget::External { target, .. } = &edge.target {
                targets.insert(target.clone());
            }
        }
    }
    targets
}

impl CheckedModule {
    pub(crate) fn for_mode(
        t: &mut DefaultTypes,
        result: FrontendResult,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<Self, PipelineError> {
        use crate::telemetry::TelemetryExt as _;

        let frontend = run_frontend(result, tel)?;
        let interfaces = frontend._prog.module_interfaces;
        let external_interfaces = frontend._prog.external_module_interfaces;
        tel.event(
            &["fz", "module", "interfaces_collected"],
            metadata! { interfaces: interfaces.len() as i64 },
        );
        if mode.is_lto() {
            let linked = LtoLinkedProgram::validate(frontend.module, interfaces, tel, Some(&frontend.sm))?;
            let (module, interfaces) = linked.erase_boundaries(tel)?;
            let _compile_span = tel.span(
                &["fz", "compile"],
                metadata! {
                    compile_nonce: next_compile_nonce(),
                    module_path: module.module_path().to_owned(),
                },
            );
            let module_plan = plan_module(t, &module, tel);
            return Ok(Self {
                module,
                module_plan,
                interfaces,
                external_interfaces,
                sm: frontend.sm,
                diagnostics: frontend.diagnostics,
            });
        }
        Ok(Self {
            module: frontend.module,
            module_plan: frontend.module_plan,
            interfaces,
            external_interfaces,
            sm: frontend.sm,
            diagnostics: frontend.diagnostics,
        })
    }
}

impl CompilerWorld {
    pub(crate) fn prepare_execution_graph(
        &mut self,
        t: &mut DefaultTypes,
        mut checked: CheckedModule,
        tel: &dyn Telemetry,
        mode: CompileMode,
    ) -> Result<PreparedExecutionGraph, PipelineError> {
        use crate::telemetry::TelemetryExt as _;

        let linked = self.link_execution_module(t, &mut checked, tel)?;
        let LinkedExecutionModule { units, module } = linked;
        let _compile_span = tel.span(
            &["fz", "compile"],
            metadata! {
                compile_nonce: next_compile_nonce(),
                module_path: module.module_path().to_owned(),
            },
        );
        let module_plan = plan_module(t, &module, tel);
        if mode.is_lto() {
            let interfaces = units
                .iter()
                .filter_map(|unit| {
                    unit.interface
                        .clone()
                        .map(|interface| (interface.name.clone(), interface))
                })
                .collect();
            let linked = LtoLinkedProgram::validate(module.clone(), interfaces, tel, Some(&checked.sm))?;
            let (module, _) = linked.erase_boundaries(tel)?;
            let module_plan = plan_module(t, &module, tel);
            return Ok(PreparedExecutionGraph {
                units,
                module,
                module_plan,
                sm: checked.sm,
            });
        }
        Ok(PreparedExecutionGraph {
            units,
            module,
            module_plan,
            sm: checked.sm,
        })
    }

    pub(crate) fn link_execution_module(
        &mut self,
        t: &mut DefaultTypes,
        checked: &mut CheckedModule,
        tel: &dyn Telemetry,
    ) -> Result<LinkedExecutionModule, PipelineError> {
        let units = self.load_execution_units(t, checked, tel)?;
        let module = if units.len() > 1 {
            link_ir_units(&units).map_err(PipelineError::Link)?
        } else {
            units[0].code.clone()
        };
        Ok(LinkedExecutionModule { units, module })
    }

    fn load_execution_units(
        &mut self,
        t: &mut DefaultTypes,
        checked: &mut CheckedModule,
        tel: &dyn Telemetry,
    ) -> Result<Vec<CompiledUnit>, PipelineError> {
        let seeds = self.runtime_reachability_seeds(&checked.module, &checked.module_plan, tel)?;
        let mut pending_runtime_modules = self
            .discover_runtime_reachable_modules(&checked.interfaces, seeds, tel)
            .map_err(|diagnostic| {
                emit_through(tel, None, &[diagnostic]);
                PipelineError::FrontendFailed
            })?;
        let mut interfaces = checked.interfaces.clone();
        interfaces.extend(checked.external_interfaces.clone());
        let mut units = vec![checked.compiled_unit_input()];
        let empty_root_interfaces = BTreeMap::new();
        while let Some(module_id) = pending_runtime_modules.pop() {
            let ModuleKey::Named(module_name) = self.module(module_id).key.clone() else {
                continue;
            };
            let Some(interface) = self
                .ensure_runtime_module_interface(&module_name, tel)
                .map_err(|diagnostic| {
                    emit_through(tel, None, &[diagnostic]);
                    PipelineError::FrontendFailed
                })?
            else {
                continue;
            };
            interfaces.insert(module_name, interface);
            let Some(unit) = self.materialize_runtime_unit(t, module_id, &interfaces, tel)? else {
                continue;
            };
            let follow_up_seeds = unit
                .module_plan
                .as_ref()
                .map(|plan| self.runtime_reachability_seeds(&unit.code, plan, tel))
                .transpose()?
                .unwrap_or_default();
            if !follow_up_seeds.is_empty() {
                let newly_reachable = self
                    .discover_runtime_reachable_modules(&empty_root_interfaces, follow_up_seeds, tel)
                    .map_err(|diagnostic| {
                        emit_through(tel, None, &[diagnostic]);
                        PipelineError::FrontendFailed
                    })?;
                pending_runtime_modules.extend(newly_reachable);
            }
            units.push(unit);
        }
        tel.event(
            &["fz", "module", "execution_units_prepared"],
            metadata! {
                interfaces: interfaces.len() as i64,
                runtime_units: (units.len() - 1) as i64,
                total_units: units.len() as i64,
            },
        );
        Ok(units)
    }

    fn materialize_runtime_unit(
        &mut self,
        t: &mut DefaultTypes,
        module_id: ModuleId,
        interfaces: &InterfaceTable,
        tel: &dyn Telemetry,
    ) -> Result<Option<CompiledUnit>, PipelineError> {
        let ModuleKey::Named(module_name) = self.module(module_id).key.clone() else {
            return Ok(None);
        };
        let parsed = self.ensure_prelude(module_id, tel).map_err(|diagnostic| {
            emit_through(tel, None, &[diagnostic]);
            PipelineError::FrontendFailed
        })?;
        let program = crate::ast::Program {
            items: parsed.items,
            ..crate::ast::Program::default()
        };
        let frontend =
            run_frontend(self.compile_program_from_roots(None, Some(module_id), t, program, parsed.sm, interfaces.clone(), tel), tel)?;
        let _ = self.note_runtime_lowered(module_id, frontend.module.fns.len(), tel);
        let _ = self.note_runtime_planned(module_id, frontend.module_plan.specs.len(), tel);
        tel.event(
            &["fz", "module", "unit_materialized"],
            metadata! { kind: "runtime-source", module: module_name.dotted() },
        );
        Ok(Some(CompiledUnit::from_ir_module_with_plan(
            frontend.module,
            Some(frontend.module_plan),
            interfaces.get(&module_name).cloned(),
            Diagnostics::new(),
        )))
    }

    fn runtime_reachability_seeds(
        &mut self,
        module: &Module,
        module_plan: &ModulePlan,
        tel: &dyn Telemetry,
    ) -> Result<Vec<RuntimeReachabilitySeed>, PipelineError> {
        let mut targets = BTreeSet::new();
        targets.extend(module.external_call_edges.iter().map(|edge| edge.target.clone()));
        targets.extend(planned_external_targets(module_plan));

        let mut seeds = Vec::new();
        for target in targets {
            let Some(owner_module_id) = self
                .discover_runtime_export_owner(&target, tel)
                .map_err(|diagnostic| {
                    emit_through(tel, None, &[diagnostic]);
                    PipelineError::FrontendFailed
                })?
            else {
                continue;
            };
            let ModuleKey::Named(owner_module) = self.module(owner_module_id).key.clone() else {
                continue;
            };
            let entry = format!("{}.{}", target.module.dotted(), target.name);
            seeds.push(
                RuntimeReachabilitySeed::new(owner_module, "planned_external_target", None)
                    .with_entry(entry, target.arity),
            );
        }
        Ok(seeds)
    }
}

struct LtoLinkedProgram {
    module: Module,
    interfaces: BTreeMap<ModuleName, ModuleInterface>,
}

impl LtoLinkedProgram {
    fn validate(
        module: Module,
        interfaces: BTreeMap<ModuleName, ModuleInterface>,
        tel: &dyn Telemetry,
        sm: Option<&SourceMap>,
    ) -> Result<Self, PipelineError> {
        let diags = validate_public_export_specs(&interfaces);
        if !diags.is_empty() {
            emit_through(tel, sm, &diags);
            return Err(PipelineError::LtoInterfaceSpecs);
        }
        tel.event(
            &["fz", "lto", "interfaces_validated"],
            metadata! { interfaces: interfaces.len() as i64 },
        );
        Ok(Self { module, interfaces })
    }

    fn erase_boundaries(
        mut self,
        tel: &dyn Telemetry,
    ) -> Result<(Module, BTreeMap<ModuleName, ModuleInterface>), PipelineError> {
        let exports = self.module.interface_export_map(&self.interfaces);
        let rewritten = self.module.rewrite_external_calls_for_lto(&exports).map_err(|err| {
            let diagnostic = Diagnostic::error(LOWER_UNBOUND, err.to_string(), Span::DUMMY);
            emit_through(tel, None, &[diagnostic]);
            PipelineError::LtoRewriteFailed
        })?;
        let erased_boundaries = self.module.boundary_fns.len();
        self.module.boundary_fns.clear();
        tel.event(
            &["fz", "lto", "boundaries_erased"],
            metadata! { rewritten: rewritten as i64, spec_boundaries: erased_boundaries as i64 },
        );
        Ok((self.module, self.interfaces))
    }
}

#[cfg(test)]
#[path = "pipeline_test.rs"]
mod pipeline_test;
