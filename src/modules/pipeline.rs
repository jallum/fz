//! Module-aware frontend and execution-graph preparation.

#![allow(clippy::result_large_err)]

use crate::diag::{self, Diagnostic};
use crate::frontend;
use crate::fz_ir;
use crate::ir_codegen::{self, CompiledUnit, ImageLinkError};
use crate::ir_planner;
use crate::metadata;
use crate::modules::artifact_store::{ArtifactStore, ArtifactStoreError};
use crate::modules::graph::ModuleGraphLoader;
use crate::modules::identity::ModuleName;
use crate::modules::interface::{ModuleInterface, validate_public_export_specs};
use crate::resolve::InterfaceTable;
use crate::telemetry;
use crate::types;
use std::collections::BTreeMap;

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

#[derive(Clone, Debug)]
pub(crate) struct ProviderInputs {
    pub(crate) artifact_root: String,
    pub(crate) modules: Vec<ModuleName>,
}

impl ProviderInputs {
    pub(crate) fn new(artifact_root: String, modules: Vec<ModuleName>) -> Self {
        Self {
            artifact_root,
            modules,
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.modules.is_empty()
    }
}

pub(crate) struct CheckedModule {
    pub(crate) module: fz_ir::Module,
    pub(crate) module_plan: ir_planner::ModulePlan,
    pub(crate) interfaces: BTreeMap<ModuleName, ModuleInterface>,
    pub(crate) external_interfaces: BTreeMap<ModuleName, ModuleInterface>,
    pub(crate) sm: diag::SourceMap,
    pub(crate) diagnostics: diag::Diagnostics,
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
        CompiledUnit::from_ir_module(self.module.clone(), interface, diag::Diagnostics::new())
    }
}

pub(crate) struct PreparedExecutionGraph {
    pub(crate) units: Vec<CompiledUnit>,
    pub(crate) module: fz_ir::Module,
    pub(crate) module_plan: ir_planner::ModulePlan,
    pub(crate) sm: diag::SourceMap,
}

pub(crate) enum PipelineError {
    Frontend(frontend::FrontendErr),
    Diagnostics {
        sm: Option<diag::SourceMap>,
        diagnostics: diag::Diagnostics,
    },
    DiagnosticVec {
        sm: Option<diag::SourceMap>,
        diagnostics: Vec<Diagnostic>,
    },
    Diagnostic(Diagnostic),
    Artifact(ArtifactStoreError),
    Link(ImageLinkError),
    MissingFzoModule,
}

pub(crate) fn load_interface_table(
    artifact_root: &str,
    modules: &[ModuleName],
    tel: &dyn telemetry::Telemetry,
) -> Result<InterfaceTable, PipelineError> {
    let store = ArtifactStore::new(artifact_root);
    store
        .load_interface_table_with_telemetry(tel, modules)
        .map_err(PipelineError::Artifact)
}

pub(crate) fn compile_source_with_providers(
    t: &mut types::ConcreteTypes,
    src: String,
    source_name: String,
    providers: &ProviderInputs,
    tel: &dyn telemetry::Telemetry,
) -> Result<frontend::FrontendResult, PipelineError> {
    if providers.is_empty() {
        Ok(frontend::compile_source_with_types(
            t,
            src,
            source_name,
            tel,
        ))
    } else {
        let interfaces = load_interface_table(&providers.artifact_root, &providers.modules, tel)?;
        Ok(frontend::compile_source_with_interface_table(
            t,
            src,
            source_name,
            interfaces,
            tel,
        ))
    }
}

pub(crate) fn checked_module_for_mode(
    t: &mut types::ConcreteTypes,
    result: frontend::FrontendResult,
    tel: &dyn telemetry::Telemetry,
    mode: CompileMode,
) -> Result<CheckedModule, PipelineError> {
    let frontend = run_frontend(result)?;
    let interfaces = frontend._prog.module_interfaces;
    let external_interfaces = frontend._prog.external_module_interfaces;
    tel.event(
        &["fz", "module", "interfaces_collected"],
        metadata! { interfaces: interfaces.len() as i64 },
    );
    if mode.is_lto() {
        let linked =
            LtoLinkedProgram::validate(frontend.module, interfaces, tel, Some(&frontend.sm))?;
        let (module, interfaces) = linked.erase_boundaries(tel)?;
        let module_plan = ir_planner::plan_module(t, &module, tel);
        Ok(CheckedModule {
            module,
            module_plan,
            interfaces,
            external_interfaces,
            sm: frontend.sm,
            diagnostics: frontend.diagnostics,
        })
    } else {
        Ok(CheckedModule {
            module: frontend.module,
            module_plan: frontend.module_plan,
            interfaces,
            external_interfaces,
            sm: frontend.sm,
            diagnostics: frontend.diagnostics,
        })
    }
}

pub(crate) fn prepare_execution_graph(
    t: &mut types::ConcreteTypes,
    prepared: CheckedModule,
    providers: &ProviderInputs,
    tel: &dyn telemetry::Telemetry,
    mode: CompileMode,
) -> Result<PreparedExecutionGraph, PipelineError> {
    let units = load_provider_units(t, &prepared, providers, tel)?;
    let linked_units = units.len() > 1;
    let module = if !linked_units {
        units[0].code.clone()
    } else {
        ir_codegen::link_ir_units(&units).map_err(PipelineError::Link)?
    };
    let module_plan = if !linked_units {
        prepared.module_plan
    } else if mode.is_lto() {
        let interfaces = units
            .iter()
            .filter_map(|unit| {
                unit.interface
                    .clone()
                    .map(|interface| (interface.name.clone(), interface))
            })
            .collect();
        let linked =
            LtoLinkedProgram::validate(module.clone(), interfaces, tel, Some(&prepared.sm))?;
        let (module, _) = linked.erase_boundaries(tel)?;
        return Ok(PreparedExecutionGraph {
            units,
            module_plan: ir_planner::plan_module(t, &module, tel),
            module,
            sm: prepared.sm,
        });
    } else {
        ir_planner::plan_module(t, &module, tel)
    };
    Ok(PreparedExecutionGraph {
        units,
        module,
        module_plan,
        sm: prepared.sm,
    })
}

pub(crate) fn link_error_diagnostic(err: ImageLinkError) -> Diagnostic {
    Diagnostic::error(
        diag::codes::CODEGEN_SCHEMA_MISSING,
        err.to_string(),
        diag::Span::DUMMY,
    )
}

fn run_frontend(result: frontend::FrontendResult) -> Result<frontend::FrontendOk, PipelineError> {
    let ok = result.map_err(PipelineError::Frontend)?;
    if has_errors(&ok.diagnostics) {
        return Err(PipelineError::Diagnostics {
            sm: Some(ok.sm.clone()),
            diagnostics: ok.diagnostics,
        });
    }
    Ok(ok)
}

fn has_errors(diagnostics: &diag::Diagnostics) -> bool {
    diagnostics
        .as_slice()
        .iter()
        .any(|diagnostic| diagnostic.severity == diag::diagnostic::Severity::Error)
}

fn load_provider_units(
    t: &mut types::ConcreteTypes,
    prepared: &CheckedModule,
    providers: &ProviderInputs,
    tel: &dyn telemetry::Telemetry,
) -> Result<Vec<CompiledUnit>, PipelineError> {
    let store = ArtifactStore::new(&providers.artifact_root);
    let runtime_roots = prepared
        .external_interfaces
        .keys()
        .filter(|module| crate::modules::runtime_library::interface(module).is_some())
        .cloned();
    let provider_roots = providers
        .modules
        .iter()
        .cloned()
        .chain(runtime_roots)
        .collect::<Vec<_>>();
    let graph = ModuleGraphLoader::new(store)
        .load_reachable(&prepared.interfaces, &provider_roots)
        .map_err(PipelineError::Artifact)?;
    tel.event(
        &["fz", "module", "graph_loaded"],
        metadata! {
            interfaces: graph.interfaces.len() as i64,
            objects: graph.objects.len() as i64,
        },
    );

    let mut units = vec![prepared.compiled_unit_input()];
    for object in graph.objects {
        let module = object
            .module
            .clone()
            .ok_or(PipelineError::MissingFzoModule)?;
        let source = object
            .source_unit_text()
            .map_err(PipelineError::Diagnostic)?;
        let frontend = run_frontend(frontend::compile_source_with_interface_table(
            t,
            source.to_string(),
            format!("artifact:{module}"),
            graph.interfaces.clone(),
            tel,
        ))?;
        let interface = graph.interfaces.get(&module).cloned();
        units.push(CompiledUnit::from_ir_module(
            frontend.module,
            interface,
            diag::Diagnostics::new(),
        ));
    }
    Ok(units)
}

struct LtoLinkedProgram {
    module: fz_ir::Module,
    interfaces: BTreeMap<ModuleName, ModuleInterface>,
}

impl LtoLinkedProgram {
    fn validate(
        module: fz_ir::Module,
        interfaces: BTreeMap<ModuleName, ModuleInterface>,
        tel: &dyn telemetry::Telemetry,
        sm: Option<&diag::SourceMap>,
    ) -> Result<Self, PipelineError> {
        let diags = validate_public_export_specs(&interfaces);
        if !diags.is_empty() {
            return Err(PipelineError::DiagnosticVec {
                sm: sm.cloned(),
                diagnostics: diags,
            });
        }
        tel.event(
            &["fz", "lto", "interfaces_validated"],
            metadata! { interfaces: interfaces.len() as i64 },
        );
        Ok(Self { module, interfaces })
    }

    fn erase_boundaries(
        mut self,
        tel: &dyn telemetry::Telemetry,
    ) -> Result<(fz_ir::Module, BTreeMap<ModuleName, ModuleInterface>), PipelineError> {
        let exports = self.module.interface_export_map(&self.interfaces);
        let rewritten = self
            .module
            .rewrite_external_calls_for_lto(&exports)
            .map_err(|err| {
                PipelineError::Diagnostic(Diagnostic::error(
                    diag::codes::LOWER_UNBOUND,
                    err.to_string(),
                    diag::Span::DUMMY,
                ))
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
mod tests {
    use super::*;

    #[test]
    fn execution_graph_loads_runtime_import_without_user_providers() {
        let mut concrete_types = types::ConcreteTypes;
        let tel = telemetry::NullTelemetry;
        let providers = ProviderInputs::new(
            std::env::temp_dir()
                .join(format!("fz-runtime-graph-{}", std::process::id()))
                .display()
                .to_string(),
            Vec::new(),
        );
        let source = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  fn run(bytes), do: valid?(bytes)
end
"#;

        let frontend = compile_source_with_providers(
            &mut concrete_types,
            source.to_string(),
            "user.fz".to_string(),
            &providers,
            &tel,
        )
        .unwrap_or_else(|_| panic!("frontend result"));
        let checked =
            checked_module_for_mode(&mut concrete_types, frontend, &tel, CompileMode::Normal)
                .unwrap_or_else(|_| panic!("checked module"));
        let graph = prepare_execution_graph(
            &mut concrete_types,
            checked,
            &providers,
            &tel,
            CompileMode::Normal,
        )
        .unwrap_or_else(|_| panic!("execution graph"));

        let modules = graph
            .units
            .iter()
            .filter_map(|unit| unit.module.as_ref().map(ModuleName::dotted))
            .collect::<Vec<_>>();
        assert!(modules.contains(&"User".to_string()));
        assert!(modules.contains(&"Utf8".to_string()));
        assert!(!modules.contains(&"Process".to_string()));
    }
}
