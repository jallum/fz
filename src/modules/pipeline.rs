//! Module-aware frontend and execution-graph preparation.

use crate::compiler::source::{SourceMap, Span};
use crate::diag::codes::{CODEGEN_SCHEMA_MISSING, LOWER_UNBOUND};
use crate::diag::diagnostic::Severity;
use crate::diag::{Diagnostic, Diagnostics, emit_through};
use crate::frontend::{FrontendOk, FrontendResult, compile_source_with_interface_table};
use crate::fz_ir::Module;
use crate::ir_codegen::{CompiledUnit, ImageLinkError, link_ir_units};
use crate::ir_planner::{ModulePlan, plan_module_with_role};
use crate::metadata;
use crate::modules::graph::ModuleGraphLoader;
use crate::modules::identity::ModuleName;
use crate::modules::interface::{ModuleInterface, validate_public_export_specs};
use crate::modules::runtime_library;
use crate::telemetry::{Telemetry, next_compile_nonce};
use crate::types::DefaultTypes;
use std::collections::BTreeMap;
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
    pub(crate) diagnostics: Diagnostics,
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

pub(crate) fn checked_module_for_mode(
    t: &mut DefaultTypes,
    result: FrontendResult,
    tel: &dyn Telemetry,
    mode: CompileMode,
) -> Result<CheckedModule, PipelineError> {
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
        let module_plan = plan_module_with_role(t, &module, tel, "lto_boundary_erased");
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
    t: &mut DefaultTypes,
    mut prepared: CheckedModule,
    tel: &dyn Telemetry,
    mode: CompileMode,
) -> Result<PreparedExecutionGraph, PipelineError> {
    use crate::telemetry::TelemetryExt as _;

    let diagnostics = prepared.diagnostics.clone();
    let sm = prepared.sm.clone();
    let linked = link_execution_module(t, &mut prepared, tel)?;
    let LinkedExecutionModule { units, module } = linked;
    let _compile_span = tel.span(
        &["fz", "compile"],
        metadata! {
            compile_nonce: next_compile_nonce(),
            module_path: module.module_path().to_owned(),
        },
    );
    let module_plan = plan_module_with_role(t, &module, tel, "linked_execution_graph");
    // The execution graph hands downstream engines the real linked module and
    // its one authoritative plan. Mutating IR transforms that change dispatch
    // or reachability must not run here unless they also preserve that
    // contract; otherwise they erase facts the planner still needs to observe.
    // LTO mode still runs boundary erasure for its module-mutating side effect
    // (rewriting external calls to direct ones); its local plan is discarded.
    if mode.is_lto() {
        let interfaces = units
            .iter()
            .filter_map(|unit| {
                unit.interface
                    .clone()
                    .map(|interface| (interface.name.clone(), interface))
            })
            .collect();
        let linked = LtoLinkedProgram::validate(module.clone(), interfaces, tel, Some(&prepared.sm))?;
        let (module, _) = linked.erase_boundaries(tel)?;
        let module_plan = plan_module_with_role(t, &module, tel, "lto_linked_execution_graph");
        return Ok(PreparedExecutionGraph {
            units,
            module,
            module_plan,
            sm,
            diagnostics,
        });
    }
    Ok(PreparedExecutionGraph {
        units,
        module,
        module_plan,
        sm,
        diagnostics,
    })
}

pub(crate) fn link_execution_module(
    t: &mut DefaultTypes,
    prepared: &mut CheckedModule,
    tel: &dyn Telemetry,
) -> Result<LinkedExecutionModule, PipelineError> {
    let units = load_runtime_units(t, prepared, tel)?;
    let module = if units.len() > 1 {
        link_ir_units(&units).map_err(PipelineError::Link)?
    } else {
        units[0].code.clone()
    };
    Ok(LinkedExecutionModule { units, module })
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

fn load_runtime_units(
    t: &mut DefaultTypes,
    prepared: &mut CheckedModule,
    tel: &dyn Telemetry,
) -> Result<Vec<CompiledUnit>, PipelineError> {
    let runtime_roots = prepared
        .external_interfaces
        .keys()
        .filter(|module| {
            runtime_library::interface(module, tel).is_some() && !runtime_library::is_core_prelude_module(module)
        })
        .cloned();
    let runtime_roots = runtime_library::prelude_required_modules(tel)
        .into_iter()
        .chain(runtime_roots)
        .collect::<Vec<_>>();
    let graph = ModuleGraphLoader::new().load_reachable(tel, &prepared.interfaces, &runtime_roots);
    tel.event(
        &["fz", "module", "graph_loaded"],
        metadata! {
            interfaces: graph.interfaces.len() as i64,
            runtime_modules: graph.runtime_modules.len() as i64,
        },
    );

    let mut units = vec![prepared.compiled_unit_input()];
    for module in graph.runtime_modules {
        let interface = graph.interfaces.get(&module).cloned();
        let source = runtime_library::source(&module).expect("runtime module source is registered");
        let frontend = run_frontend(
            compile_source_with_interface_table(
                t,
                source.to_string(),
                format!("runtime:{module}"),
                graph.interfaces.clone(),
                tel,
            ),
            tel,
        )?;
        tel.event(
            &["fz", "module", "unit_materialized"],
            metadata! { kind: "runtime-source", module: module.dotted() },
        );
        units.push(CompiledUnit::from_ir_module_with_plan(
            frontend.module,
            Some(frontend.module_plan),
            interface,
            Diagnostics::new(),
        ));
    }
    Ok(units)
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
