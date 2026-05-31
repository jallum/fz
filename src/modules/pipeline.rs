//! Module-aware frontend and execution-graph preparation.

use crate::diag::{self, Diagnostic};
use crate::frontend;
use crate::frontend::resolve::InterfaceTable;
use crate::fz_ir;
use crate::ir_codegen::{self, CompiledUnit, ImageLinkError};
use crate::ir_planner;
use crate::metadata;
use crate::modules::artifact_store::{ArtifactStore, ArtifactStoreError};
use crate::modules::graph::ModuleGraphLoader;
use crate::modules::identity::ModuleName;
use crate::modules::interface::{ModuleInterface, validate_public_export_specs};
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
    mut prepared: CheckedModule,
    providers: &ProviderInputs,
    tel: &dyn telemetry::Telemetry,
    mode: CompileMode,
) -> Result<PreparedExecutionGraph, PipelineError> {
    let units = load_provider_units(t, &mut prepared, providers, tel)?;
    let linked_units = units.len() > 1;
    let mut module = if linked_units {
        ir_codegen::link_ir_units(&units).map_err(PipelineError::Link)?
    } else {
        units[0].code.clone()
    };
    if !module.protocol_call_targets.is_empty() {
        let mut module_plan = ir_planner::plan_module(t, &module, tel);
        frontend::apply_planner_rewrites_to_fixed_point(t, &mut module, &mut module_plan);
    }
    // Codegen re-plans the linked working module itself (see
    // `compile_with_backend_impl`), so no plan is threaded out of here. LTO
    // mode still runs boundary erasure for its module-mutating side effect
    // (rewriting external calls to direct ones); its plan is discarded.
    if mode.is_lto() {
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
            module,
            sm: prepared.sm,
        });
    }
    Ok(PreparedExecutionGraph {
        units,
        module,
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

#[allow(clippy::too_many_arguments)]
fn load_provider_units(
    t: &mut types::ConcreteTypes,
    prepared: &mut CheckedModule,
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
        let interface = graph.interfaces.get(&module).cloned();
        if object.unit_payload.format == crate::modules::artifact::FZO_PAYLOAD_IR_UNIT_V1 {
            units.push(materialize_ir_unit(
                t,
                object,
                &module,
                interface,
                &mut prepared.sm,
                tel,
            )?);
        } else {
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
            tel.event(
                &["fz", "module", "unit_materialized"],
                metadata! { kind: "source", module: module.dotted() },
            );
            units.push(CompiledUnit::from_ir_module_with_plan(
                frontend.module,
                Some(frontend.module_plan),
                interface,
                diag::Diagnostics::new(),
            ));
        }
    }
    Ok(units)
}

/// Materialize a provider from a STRUCTURAL `.fzo` (`FZO_PAYLOAD_IR_UNIT_V1`)
/// WITHOUT recompiling from source: decode the serde `Module` plus its source
/// files, merge those files into the consumer `SourceMap` (so provider spans
/// render real diagnostics), remap the module's `FileId`s onto the interned
/// consumer ids, rebuild the derived indices the serde form drops, and re-plan
/// at load (the plan regenerates the protocol provider-boundary facts that link
/// depends on).
fn materialize_ir_unit(
    t: &mut types::ConcreteTypes,
    object: crate::modules::artifact::FzoArtifact,
    module_name: &ModuleName,
    interface: Option<ModuleInterface>,
    sm: &mut diag::SourceMap,
    tel: &dyn telemetry::Telemetry,
) -> Result<CompiledUnit, PipelineError> {
    let crate::modules::artifact::IrUnitPayload {
        mut module,
        sources,
    } = object
        .ir_unit_payload()
        .map_err(|_err| PipelineError::ArtifactPayload)?;
    let mut remap = std::collections::HashMap::new();
    for p in &sources {
        let cid = sm.intern(p.name.clone(), p.bytes.clone());
        remap.insert(p.file, cid);
    }
    module.remap_file_ids(&remap);
    module.rebuild_indices();
    let module_plan = ir_planner::plan_module(t, &module, tel);
    tel.event(
        &["fz", "module", "unit_materialized"],
        metadata! { kind: "ir-unit", module: module_name.dotted() },
    );
    Ok(CompiledUnit::from_ir_module_with_plan(
        module,
        Some(module_plan),
        interface,
        diag::Diagnostics::new(),
    ))
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

    #[test]
    fn protocol_impl_reduce_callback_plans_to_fixed_point() {
        let mut concrete_types = types::ConcreteTypes;
        let tel = telemetry::ConfiguredTelemetry::new();
        let capture = telemetry::Capture::new();
        tel.attach(&["fz", "planner", "planned"], capture.handler());
        let providers = ProviderInputs::new(
            std::env::temp_dir()
                .join(format!("fz-protocol-reduce-{}", std::process::id()))
                .display()
                .to_string(),
            Vec::new(),
        );
        let source = r#"
defprotocol Reducible do
  fn reduce(value, acc, reducer)
end

defmodule List do
  fn reduce([], {:cont, acc}, _reducer), do: {:done, acc}
  fn reduce([head | tail], {:cont, acc}, reducer), do: reduce(tail, reducer.(head, acc), reducer)
  fn reduce(_list, {:halt, acc}, _reducer), do: {:halted, acc}
end

defimpl Reducible, for: List do
  fn reduce(list, acc, reducer), do: List.reduce(list, acc, reducer)
end

fn main() do
  Reducible.reduce([1, 2, 3], {:cont, 0}, fn (x, acc) -> {:cont, x + acc} end)
end
"#;

        let frontend = compile_source_with_providers(
            &mut concrete_types,
            source.to_string(),
            "protocol_reduce.fz".to_string(),
            &providers,
            &tel,
        )
        .unwrap_or_else(|_| panic!("frontend result"));
        let checked =
            checked_module_for_mode(&mut concrete_types, frontend, &tel, CompileMode::Normal)
                .unwrap_or_else(|_| panic!("checked module"));
        prepare_execution_graph(
            &mut concrete_types,
            checked,
            &providers,
            &tel,
            CompileMode::Normal,
        )
        .unwrap_or_else(|_| panic!("execution graph"));

        let max_pops = capture
            .find(&["fz", "planner", "planned"])
            .iter()
            .filter_map(|ev| match ev.measurements.get("worklist_pops") {
                Some(telemetry::Value::U64(pops)) => Some(*pops),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        assert!(
            max_pops <= 100,
            "protocol reduce planning should converge without oscillating; max pops {max_pops}"
        );
    }

    /// Provider source whose `Contracts.Collectable.id/1` impl returns 42. The
    /// fixed return makes the consumer's dispatch observable end-to-end.
    const PROVIDER_SRC: &str = r#"defmodule Contracts do
  defprotocol Collectable do
    fn id(value)
  end

  defimpl Collectable, for: List do
    fn id(value), do: 42
  end
end
"#;

    /// Consumer that calls the provider's protocol through a provider-boundary
    /// call edge, then a top-level `main` to run.
    const CONSUMER_SRC: &str = r#"defmodule User do
  fn run(), do: Contracts.Collectable.id([1])
end
fn main(), do: User.run()
"#;

    struct StructuralProviderFixture {
        artifact_root: String,
    }

    impl Drop for StructuralProviderFixture {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.artifact_root);
        }
    }

    /// Compile `PROVIDER_SRC` through the real frontend, then emit it as a
    /// STRUCTURAL `.fzo` (`from_unit_ir`, carrying the module's real source
    /// files) plus its `.fzi` into a fresh temp `ArtifactStore`. This is exactly
    /// the production `fz build` emit shape, so the consumer below loads the
    /// provider structurally — no recompile.
    fn write_structural_provider(tag: &str) -> (StructuralProviderFixture, ModuleName) {
        let mut t = types::ConcreteTypes;
        let tel = telemetry::NullTelemetry;
        let provider = crate::frontend::compile_source_with_types(
            &mut t,
            PROVIDER_SRC.to_string(),
            "contracts.fz".to_string(),
            &tel,
        )
        .unwrap_or_else(|err| panic!("provider frontend: {:?}", err.diagnostics));
        let contracts = ModuleName::from_segments(vec!["Contracts".to_string()]);
        let interface = provider._prog.module_interfaces[&contracts].clone();

        let unit = CompiledUnit::from_ir_module_with_plan(
            provider.module,
            Some(provider.module_plan),
            Some(interface.clone()),
            diag::Diagnostics::new(),
        );
        let sources = unit
            .code
            .referenced_files()
            .into_iter()
            .map(|fid| provider.sm.file(fid).to_portable(fid))
            .collect::<Vec<_>>();
        assert!(
            !sources.is_empty(),
            "provider module must reference at least one source file"
        );
        let fzo = crate::modules::artifact::FzoArtifact::from_unit_ir(&unit, sources, Vec::new());
        assert_eq!(
            fzo.unit_payload.format,
            crate::modules::artifact::FZO_PAYLOAD_IR_UNIT_V1
        );

        let artifact_root = std::env::temp_dir()
            .join(format!("fz-structural-load-{}-{}", std::process::id(), tag))
            .display()
            .to_string();
        let _ = std::fs::remove_dir_all(&artifact_root);
        let store = crate::modules::artifact_store::ArtifactStore::new(&artifact_root);
        let mut interfaces = BTreeMap::new();
        interfaces.insert(contracts.clone(), interface);
        store.write_fzi_artifacts(&tel, &interfaces).unwrap();
        store.write_fzo_artifacts(&tel, [&fzo]).unwrap();

        (StructuralProviderFixture { artifact_root }, contracts)
    }

    /// Drive `CONSUMER_SRC` through the production pipeline against a structural
    /// provider in `root`, returning the prepared graph and the consumer's
    /// SourceMap (which the loader merges provider sources into).
    fn prepare_consumer_against(
        root: &str,
        provider: &ModuleName,
        tel: &dyn telemetry::Telemetry,
    ) -> PreparedExecutionGraph {
        let mut t = types::ConcreteTypes;
        let providers = ProviderInputs::new(root.to_string(), vec![provider.clone()]);
        let frontend = compile_source_with_providers(
            &mut t,
            CONSUMER_SRC.to_string(),
            "user.fz".to_string(),
            &providers,
            tel,
        )
        .unwrap_or_else(|_| panic!("consumer frontend"));
        let checked = checked_module_for_mode(&mut t, frontend, tel, CompileMode::Normal)
            .unwrap_or_else(|_| panic!("checked module"));
        prepare_execution_graph(&mut t, checked, &providers, tel, CompileMode::Normal)
            .unwrap_or_else(|err| panic!("execution graph: {err:?}"))
    }

    /// Gate 1: a structurally-loaded provider links and runs WITHOUT recompiling
    /// from source — the consumer's protocol dispatch reaches the provider's
    /// impl and returns 42.
    #[test]
    fn structural_provider_loads_and_runs_without_recompile() {
        let tel = telemetry::NullTelemetry;
        let (fixture, provider) = write_structural_provider("run");
        let graph = prepare_consumer_against(&fixture.artifact_root, &provider, &tel);

        let module = if graph.units.len() > 1 {
            ir_codegen::link_ir_units(&graph.units).expect("link ir units")
        } else {
            graph.units[0].code.clone()
        };
        let result = crate::ir_interp::run_main(&tel, &module).expect("run linked image");
        assert_eq!(result, 42, "structural provider dispatch returns 42");
    }

    /// Gate 2: the provider was materialized structurally (`kind: "ir-unit"`) and
    /// the frontend did NOT run for it — `fz.frontend.parsed` fires once (the
    /// consumer) even though two modules are in the linked graph.
    #[test]
    fn structural_provider_is_materialized_without_frontend() {
        let tel = telemetry::ConfiguredTelemetry::new();
        let capture = telemetry::Capture::new();
        tel.attach(&["fz"], capture.handler());

        let (fixture, provider) = write_structural_provider("no-recompile");
        let _graph = prepare_consumer_against(&fixture.artifact_root, &provider, &tel);

        let materialized = capture.find(&["fz", "module", "unit_materialized"]);
        let ir_units = materialized
            .iter()
            .filter(|ev| {
                matches!(
                    ev.metadata.get("kind"),
                    Some(telemetry::Value::Str(kind)) if kind == "ir-unit"
                )
            })
            .filter(|ev| {
                matches!(
                    ev.metadata.get("module"),
                    Some(telemetry::Value::Str(m)) if m == "Contracts"
                )
            })
            .count();
        assert_eq!(
            ir_units, 1,
            "Contracts must be materialized once as an ir-unit, found events: {materialized:?}"
        );
        assert!(
            !materialized.iter().any(|ev| matches!(
                ev.metadata.get("kind"),
                Some(telemetry::Value::Str(kind)) if kind == "source"
            )),
            "no provider should take the source-recompile branch"
        );
        // The frontend ran exactly once — for the consumer. A recompiled
        // provider would parse a second time.
        assert_eq!(
            capture.count(&["fz", "frontend", "parsed"]),
            1,
            "frontend parses only the consumer, never the structural provider"
        );
    }

    /// Gate 3: provider spans render REAL diagnostics after structural load —
    /// the source-merge + FileId-remap make a non-DUMMY provider span resolve
    /// against the consumer's SourceMap to the provider's actual source line.
    #[test]
    fn structural_provider_spans_resolve_to_real_source() {
        let tel = telemetry::NullTelemetry;
        let (fixture, provider) = write_structural_provider("diag");
        let graph = prepare_consumer_against(&fixture.artifact_root, &provider, &tel);

        let provider_unit = graph
            .units
            .iter()
            .find(|unit| {
                unit.module
                    .as_ref()
                    .is_some_and(|m| m.dotted() == "Contracts")
            })
            .expect("loaded provider unit present in graph");

        // A concrete, non-DUMMY span from the loaded+remapped provider module.
        let mut span = None;
        provider_unit.code.visit_spans(&mut |s| {
            if span.is_none() && !s.is_dummy() {
                span = Some(s);
            }
        });
        let span = span.expect("provider module carries a non-DUMMY span after load");

        // It resolves against the CONSUMER's SourceMap (proves the merge) to the
        // provider's real source — not DUMMY, and the snippet is provider text.
        let loc = graph.sm.locate(span);
        let snippet =
            &graph.sm.file(loc.file).bytes[loc.line_start as usize..loc.line_end as usize];
        assert!(
            PROVIDER_SRC.contains(snippet) && !snippet.trim().is_empty(),
            "remapped provider span resolves to a real provider source line, got: {snippet:?}"
        );
    }
}
