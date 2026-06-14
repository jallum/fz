use std::cell::Cell;
use std::fmt::Debug;
use std::fs::{OpenOptions, write};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::telemetry::handler::EventKind;
use crate::telemetry::{ConfiguredTelemetry, Handler, Value, opaque};

use super::artifact::{AbiReadyProgram, BackendProgram, MaterializedProgram, NativeProgram};
use super::identity::{ActivationKey, ExecutableKey, FunctionId, RootId};
use super::semantic::SemanticClosure;
use super::world::World;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DumpKind {
    Activations,
    Types,
    Materialized,
    AbiReady,
    Backend,
    Native,
    Fnir,
    Clif,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DumpSpec {
    pub(crate) kind: DumpKind,
    pub(crate) path: PathBuf,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum DumpStage {
    Semantic,
    Materialized,
    AbiReady,
    Backend,
    Native,
}

#[derive(Clone, Debug)]
pub(crate) struct TypesDump {
    pub(crate) text: String,
}

#[derive(Clone, Debug)]
pub(crate) struct ActivationsDump {
    pub(crate) text: String,
}

#[derive(Clone, Debug)]
pub(crate) struct ClifDumpEntry {
    pub(crate) fn_id: u32,
    pub(crate) fn_name: String,
    pub(crate) text: String,
}

impl DumpKind {
    pub(crate) fn required_stage(self) -> Option<DumpStage> {
        match self {
            Self::Activations | Self::Types => Some(DumpStage::Semantic),
            Self::Materialized => Some(DumpStage::Materialized),
            Self::AbiReady => Some(DumpStage::AbiReady),
            Self::Backend => Some(DumpStage::Backend),
            Self::Native | Self::Fnir => Some(DumpStage::Native),
            Self::Clif => None,
        }
    }
}

pub(crate) fn max_requested_stage(specs: &[DumpSpec]) -> Option<DumpStage> {
    specs.iter().filter_map(|spec| spec.kind.required_stage()).max()
}

pub(crate) fn parse_dump_spec(spec: &str) -> Result<DumpSpec, String> {
    if let Some((kind, path)) = spec.split_once('=') {
        let kind = parse_dump_kind_name(kind)?;
        return Ok(DumpSpec {
            kind,
            path: PathBuf::from(path),
        });
    }

    let path = PathBuf::from(spec);
    let ext = path
        .extension()
        .and_then(|ext| ext.to_str())
        .ok_or_else(|| format!("dump path `{spec}` must have an extension or use <kind>=<path>"))?;
    let kind = parse_dump_kind_name(ext)?;
    Ok(DumpSpec { kind, path })
}

pub(crate) fn install_dump_handlers(tel: &ConfiguredTelemetry, root: RootId, specs: &[DumpSpec]) {
    for spec in specs {
        match spec.kind {
            DumpKind::Types => {
                tel.attach(
                    &["fz", "compiler2", "dump", "types"],
                    boxed_text_dump_handler::<TypesDump>(&spec.path, root, "dump"),
                );
            }
            DumpKind::Activations => {
                tel.attach(
                    &["fz", "compiler2", "dump", "activations"],
                    boxed_text_dump_handler::<ActivationsDump>(&spec.path, root, "dump"),
                );
            }
            DumpKind::Materialized => {
                tel.attach(
                    &["fz", "compiler2", "materialized_program", "defined"],
                    boxed_debug_dump_handler::<MaterializedProgram>(&spec.path, root, "program"),
                );
            }
            DumpKind::AbiReady => {
                tel.attach(
                    &["fz", "compiler2", "abi_ready_program", "defined"],
                    boxed_debug_dump_handler::<AbiReadyProgram>(&spec.path, root, "program"),
                );
            }
            DumpKind::Backend => {
                tel.attach(
                    &["fz", "compiler2", "backend_program", "defined"],
                    boxed_debug_dump_handler::<BackendProgram>(&spec.path, root, "program"),
                );
            }
            DumpKind::Native => {
                tel.attach(
                    &["fz", "compiler2", "native_program", "defined"],
                    boxed_debug_dump_handler::<NativeProgram>(&spec.path, root, "program"),
                );
            }
            DumpKind::Fnir => {
                tel.attach(
                    &["fz", "compiler2", "native_program", "defined"],
                    boxed_fnir_dump_handler(&spec.path, root),
                );
            }
            DumpKind::Clif => {
                tel.attach(
                    &["fz", "compiler2", "dump", "clif"],
                    boxed_clif_dump_handler(&spec.path),
                );
            }
        }
    }
}

pub(crate) fn emit_semantic_dump_events(world: &World<'_>, root: RootId, closure: &SemanticClosure) {
    let types = TypesDump {
        text: render_types_dump(world, root, closure),
    };
    world.tel().execute(
        &["fz", "compiler2", "dump", "types"],
        &crate::measurements! { root_id: root.as_u32() },
        &crate::metadata! { dump: opaque(&types) },
    );

    let activations = ActivationsDump {
        text: render_activations_dump(world, root, closure),
    };
    world.tel().execute(
        &["fz", "compiler2", "dump", "activations"],
        &crate::measurements! { root_id: root.as_u32() },
        &crate::metadata! { dump: opaque(&activations) },
    );
}

fn boxed_text_dump_handler<T: 'static + DumpText>(
    path: &Path,
    root: RootId,
    metadata_key: &'static str,
) -> Box<dyn Handler> {
    let path = path.to_path_buf();
    let wrote = Rc::new(Cell::new(false));
    Box::new(move |ev: &crate::telemetry::Event<'_, '_, '_>| {
        if ev.kind != EventKind::Event || wrote.get() || !event_matches_root(ev, root) {
            return;
        }
        let Some(value) = ev.metadata.get(metadata_key).and_then(Value::downcast_ref::<T>) else {
            return;
        };
        write_dump_file(&path, value.dump_text());
        wrote.set(true);
    })
}

fn boxed_debug_dump_handler<T: 'static + Debug>(
    path: &Path,
    root: RootId,
    metadata_key: &'static str,
) -> Box<dyn Handler> {
    let path = path.to_path_buf();
    let wrote = Rc::new(Cell::new(false));
    Box::new(move |ev: &crate::telemetry::Event<'_, '_, '_>| {
        if ev.kind != EventKind::Event || wrote.get() || !event_matches_root(ev, root) {
            return;
        }
        let Some(value) = ev.metadata.get(metadata_key).and_then(Value::downcast_ref::<T>) else {
            return;
        };
        write_dump_file(&path, &format!("{value:#?}\n"));
        wrote.set(true);
    })
}

fn boxed_fnir_dump_handler(path: &Path, root: RootId) -> Box<dyn Handler> {
    let path = path.to_path_buf();
    let wrote = Rc::new(Cell::new(false));
    Box::new(move |ev: &crate::telemetry::Event<'_, '_, '_>| {
        if ev.kind != EventKind::Event || wrote.get() || !event_matches_root(ev, root) {
            return;
        }
        let Some(program) = ev
            .metadata
            .get("program")
            .and_then(Value::downcast_ref::<NativeProgram>)
        else {
            return;
        };
        write_dump_file(&path, &format!("{:#?}\n", program.module));
        wrote.set(true);
    })
}

fn boxed_clif_dump_handler(path: &Path) -> Box<dyn Handler> {
    let path = path.to_path_buf();
    let cleared = Rc::new(Cell::new(false));
    Box::new(move |ev: &crate::telemetry::Event<'_, '_, '_>| {
        if ev.kind != EventKind::Event {
            return;
        }
        let Some(entry) = ev.metadata.get("entry").and_then(Value::downcast_ref::<ClifDumpEntry>) else {
            return;
        };
        if !cleared.replace(true) {
            clear_dump_file(&path);
        }
        append_dump_file(
            &path,
            &format!("; fn {} ({})\n{}\n", entry.fn_name, entry.fn_id, entry.text),
        );
    })
}

trait DumpText {
    fn dump_text(&self) -> &str;
}

impl DumpText for TypesDump {
    fn dump_text(&self) -> &str {
        &self.text
    }
}

impl DumpText for ActivationsDump {
    fn dump_text(&self) -> &str {
        &self.text
    }
}

fn parse_dump_kind_name(name: &str) -> Result<DumpKind, String> {
    match name {
        "activations" | "acts" => Ok(DumpKind::Activations),
        "types" => Ok(DumpKind::Types),
        "materialized" | "mat" => Ok(DumpKind::Materialized),
        "abi" | "abiready" | "abi-ready" => Ok(DumpKind::AbiReady),
        "backend" => Ok(DumpKind::Backend),
        "native" => Ok(DumpKind::Native),
        "fnir" => Ok(DumpKind::Fnir),
        "clif" => Ok(DumpKind::Clif),
        other => Err(format!(
            "unsupported dump kind `{other}`; expected one of activations, types, materialized, abi, backend, native, fnir, clif"
        )),
    }
}

fn event_matches_root(ev: &crate::telemetry::Event<'_, '_, '_>, root: RootId) -> bool {
    matches!(ev.measurements.get("root_id"), Some(Value::U64(value)) if *value == root.as_u32() as u64)
}

fn render_types_dump(world: &World<'_>, root: RootId, closure: &SemanticClosure) -> String {
    let mut activations = root_owned_activations(world, root, closure);
    activations.sort_by_cached_key(|activation| activation_sort_key(world, activation));
    let mut out = String::new();
    for activation in activations {
        let return_ty = world
            .activation_return(&activation)
            .map(|ty| world.types().display(&ty))
            .unwrap_or_else(|| "none".to_string());
        out.push_str(&format!("{} => {}\n", activation_label(world, &activation), return_ty));
    }
    out
}

fn render_activations_dump(world: &World<'_>, root: RootId, closure: &SemanticClosure) -> String {
    let mut activations = root_owned_activations(world, root, closure);
    activations.sort_by_cached_key(|activation| activation_sort_key(world, activation));
    let mut out = String::new();
    for activation in activations {
        out.push_str(&format!("{}\n", activation_label(world, &activation)));
        let return_ty = world
            .activation_return(&activation)
            .map(|ty| world.types().display(&ty))
            .unwrap_or_else(|| "none".to_string());
        out.push_str(&format!("  return: {}\n", return_ty));

        if let Some(analysis) = world.activation_analysis(&activation) {
            let mut executables = analysis.latent_executables.clone();
            executables.sort_by_cached_key(|key| executable_sort_key(world, key));
            if !executables.is_empty() {
                out.push_str("  latent executables:\n");
                for executable in executables {
                    out.push_str(&format!("    {}\n", executable_label(world, &executable)));
                }
            }

            let mut callsites = analysis.callsites.clone();
            callsites.sort_by_key(|callsite| (callsite.span().start, callsite.span().end, callsite.as_u32()));
            if !callsites.is_empty() {
                out.push_str("  callsites:\n");
                for callsite in callsites {
                    let key = super::semantic::CallSiteKey {
                        activation: activation.clone(),
                        callsite,
                    };
                    if let Some(summary) = world.callsite_summary(&key) {
                        out.push_str(&format!(
                            "    {} => {}\n",
                            span_label(callsite.span()),
                            render_callsite_summary(world, summary)
                        ));
                    }
                }
            }
        }

        out.push('\n');
    }
    out
}

fn root_owned_activations(world: &World<'_>, root: RootId, closure: &SemanticClosure) -> Vec<ActivationKey> {
    let root_code = world.function_definition(world.root_function(root)).0.code;
    closure
        .activations
        .iter()
        .filter(|activation| world.function_definition(activation.function).0.code == root_code)
        .cloned()
        .collect()
}

fn render_callsite_summary(world: &World<'_>, summary: &super::semantic::CallSiteSummary) -> String {
    let mut targets = summary
        .targets
        .iter()
        .map(|target| {
            let target_name = match target.callee {
                super::semantic::SelectedCallee::Function(function) => function_label(world, function),
                super::semantic::SelectedCallee::ProviderBoundary(function) => {
                    format!("provider:{}", function_label(world, function))
                }
            };
            let inputs = target
                .surface_inputs
                .iter()
                .map(|ty| world.types().display(ty))
                .collect::<Vec<_>>()
                .join(", ");
            let ret = target
                .return_ty
                .map(|ty| world.types().display(&ty))
                .unwrap_or_else(|| "none".to_string());
            format!("{target_name}({inputs}) => {ret}")
        })
        .collect::<Vec<_>>();
    if targets.is_empty() {
        "no targets".to_string()
    } else {
        targets.sort();
        targets.join(" || ")
    }
}

fn activation_sort_key(world: &World<'_>, activation: &ActivationKey) -> (String, Vec<String>) {
    (
        function_label(world, activation.function),
        activation.input.iter().map(|ty| world.types().display(ty)).collect(),
    )
}

fn executable_sort_key(world: &World<'_>, executable: &ExecutableKey) -> (String, Vec<String>, String) {
    (
        function_label(world, executable.activation.function),
        executable
            .activation
            .input
            .iter()
            .map(|ty| world.types().display(ty))
            .collect(),
        format!("{:?}", executable.need),
    )
}

fn activation_label(world: &World<'_>, activation: &ActivationKey) -> String {
    let inputs = activation
        .input
        .iter()
        .map(|ty| world.types().display(ty))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}[{}]", function_label(world, activation.function), inputs)
}

fn executable_label(world: &World<'_>, executable: &ExecutableKey) -> String {
    format!(
        "{} need={:?}",
        activation_label(world, &executable.activation),
        executable.need
    )
}

fn function_label(world: &World<'_>, function: FunctionId) -> String {
    let function_ref = world.function_ref(function);
    let module = world.module_name(function_ref.module).unwrap_or_default();
    if module.is_empty() {
        format!("{}/{}", function_ref.name, function_ref.arity)
    } else {
        format!("{}.{}/{}", module, function_ref.name, function_ref.arity)
    }
}

fn span_label(span: crate::compiler::source::Span) -> String {
    if span.is_dummy() {
        "<generated>".to_string()
    } else {
        format!("@{}-{}", span.start, span.end)
    }
}

fn clear_dump_file(path: &Path) {
    write_dump_file(path, "");
}

fn append_dump_file(path: &Path, text: &str) {
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .unwrap_or_else(|error| panic!("open {} for append: {error}", path.display()));
    file.write_all(text.as_bytes())
        .unwrap_or_else(|error| panic!("append {}: {error}", path.display()));
}

fn write_dump_file(path: &Path, text: &str) {
    write(path, text).unwrap_or_else(|error| panic!("write {}: {error}", path.display()));
}
