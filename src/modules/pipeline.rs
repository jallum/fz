//! Module-aware frontend and execution-graph preparation.

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
        CompiledUnit::from_ir_module_with_plan(
            self.module.clone(),
            Some(self.module_plan.clone()),
            interface,
            diag::Diagnostics::new(),
        )
    }
}

pub(crate) struct PreparedExecutionGraph {
    pub(crate) units: Vec<CompiledUnit>,
    pub(crate) module: fz_ir::Module,
    pub(crate) module_plan: ir_planner::ModulePlan,
    pub(crate) sm: diag::SourceMap,
}

#[derive(Debug)]
pub(crate) enum PipelineError {
    FrontendFailed,
    FrontendDiagnostics,
    LtoInterfaceSpecs,
    LtoRewriteFailed,
    ArtifactPayload,
    Artifact(ArtifactStoreError),
    Link(ImageLinkError),
    MissingFzoModule,
}

impl std::fmt::Display for PipelineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FrontendFailed => f.write_str("frontend failed"),
            Self::FrontendDiagnostics => f.write_str("frontend reported errors"),
            Self::LtoInterfaceSpecs => f.write_str("LTO interface validation failed"),
            Self::LtoRewriteFailed => f.write_str("LTO rewrite failed"),
            Self::ArtifactPayload => f.write_str("artifact payload is not materializable"),
            Self::Artifact(err) => write!(f, "{err}"),
            Self::Link(err) => write!(f, "{err}"),
            Self::MissingFzoModule => f.write_str("fzo artifact has no module identity"),
        }
    }
}

impl std::error::Error for PipelineError {}

impl PipelineError {
    pub(crate) fn diagnostics_emitted(&self) -> bool {
        match self {
            Self::FrontendFailed
            | Self::FrontendDiagnostics
            | Self::LtoInterfaceSpecs
            | Self::LtoRewriteFailed
            | Self::ArtifactPayload => true,
            Self::Artifact(err) => err.diagnostics_emitted(),
            Self::Link(_) | Self::MissingFzoModule => false,
        }
    }
}

pub(crate) fn load_interface_table(
    artifact_root: &str,
    modules: &[ModuleName],
    tel: &dyn telemetry::Telemetry,
) -> Result<InterfaceTable, PipelineError> {
    let store = ArtifactStore::new(artifact_root);
    store
        .load_interface_table(tel, modules)
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
    let frontend = run_frontend(result, tel)?;
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
    let linked = if !linked_units {
        None
    } else {
        Some(ir_codegen::link_ir_units_with_plan(&units).map_err(PipelineError::Link)?)
    };
    let module = if let Some(linked) = &linked {
        linked.module.clone()
    } else {
        units[0].code.clone()
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
        linked
            .and_then(|linked| linked.module_plan)
            .ok_or_else(|| {
                PipelineError::Link(ImageLinkError::MissingPlannerFacts { module: None })
            })?
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

fn run_frontend(
    result: frontend::FrontendResult,
    tel: &dyn telemetry::Telemetry,
) -> Result<frontend::FrontendOk, PipelineError> {
    let ok = match result {
        Ok(ok) => ok,
        Err(err) => {
            diag::emit_through(tel, Some(&err.sm), err.diagnostics.as_slice());
            return Err(PipelineError::FrontendFailed);
        }
    };
    if has_errors(&ok.diagnostics) {
        diag::emit_through(tel, Some(&ok.sm), ok.diagnostics.as_slice());
        return Err(PipelineError::FrontendDiagnostics);
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
        .filter(|module| {
            crate::modules::runtime_library::interface(module).is_some()
                && !crate::modules::runtime_library::is_core_prelude_module(module)
        })
        .cloned();
    let provider_roots = providers
        .modules
        .iter()
        .cloned()
        .chain(crate::modules::runtime_library::prelude_required_modules())
        .chain(runtime_roots)
        .collect::<Vec<_>>();
    let graph = ModuleGraphLoader::new(store)
        .load_reachable(tel, &prepared.interfaces, &provider_roots)
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
            .source_unit_text(tel)
            .map_err(|_err| PipelineError::ArtifactPayload)?;
        let frontend = run_frontend(
            frontend::compile_source_with_interface_table(
                t,
                source.to_string(),
                format!("artifact:{module}"),
                graph.interfaces.clone(),
                tel,
            ),
            tel,
        )?;
        let interface = graph.interfaces.get(&module).cloned();
        units.push(CompiledUnit::from_ir_module_with_plan(
            frontend.module,
            Some(frontend.module_plan),
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
            diag::emit_through(tel, sm, &diags);
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
        tel: &dyn telemetry::Telemetry,
    ) -> Result<(fz_ir::Module, BTreeMap<ModuleName, ModuleInterface>), PipelineError> {
        let exports = self.module.interface_export_map(&self.interfaces);
        let rewritten = self
            .module
            .rewrite_external_calls_for_lto(&exports)
            .map_err(|err| {
                let diagnostic = Diagnostic::error(
                    diag::codes::LOWER_UNBOUND,
                    err.to_string(),
                    diag::Span::DUMMY,
                );
                diag::emit_through(tel, None, &[diagnostic]);
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
        ir_planner::PLAN_MODULE_CALLS.with(|count| count.set(0));
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
        let plan_calls = ir_planner::PLAN_MODULE_CALLS.with(|count| count.get());
        assert_eq!(
            plan_calls, 1,
            "provider graph preparation should plan the loaded runtime module once, \
             not replan the linked graph"
        );
    }
}
