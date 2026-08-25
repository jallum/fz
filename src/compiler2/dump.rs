use std::fs::{OpenOptions, write};
use std::io::Write as _;
use std::path::{Path, PathBuf};

use super::identity::{ActivationKey, ExecutableKey, FunctionId, RootId};
use super::world::World;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DumpKind {
    Activations,
    Types,
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
    Backend,
    Native,
}

impl DumpKind {
    pub(crate) fn required_stage(self) -> Option<DumpStage> {
        match self {
            // Types/Activations dumps are served from the product-path activation
            // inventory (see `Compiler2::emit_product_semantic_dumps`), not from a
            // staged drive, so they request no `DumpStage`.
            Self::Activations | Self::Types | Self::Clif => None,
            Self::Backend => Some(DumpStage::Backend),
            Self::Native | Self::Fnir => Some(DumpStage::Native),
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

pub(crate) trait RequestedOutputSink {
    fn wants_clif(&self) -> bool {
        false
    }
    fn semantic(&mut self, _world: &World, _root: RootId, _activations: &[ActivationKey]) {}
    fn program(&mut self, _world: &World, _root: RootId) {}
    fn clif(
        &mut self,
        _module: &crate::fz_ir::Module,
        _fn_id: crate::fz_ir::FnId,
        _function: &cranelift_codegen::ir::Function,
    ) {
    }
}

pub(crate) struct NullRequestedOutput;
impl RequestedOutputSink for NullRequestedOutput {}

pub(crate) struct FileRequestedOutput {
    root: RootId,
    specs: Vec<DumpSpec>,
    clif_cleared: bool,
}

impl FileRequestedOutput {
    pub(crate) fn new(root: RootId, specs: &[DumpSpec]) -> Self {
        Self {
            root,
            specs: specs.to_vec(),
            clif_cleared: false,
        }
    }
}

impl RequestedOutputSink for FileRequestedOutput {
    fn wants_clif(&self) -> bool {
        self.specs.iter().any(|spec| spec.kind == DumpKind::Clif)
    }

    fn semantic(&mut self, world: &World, root: RootId, activations: &[ActivationKey]) {
        if root != self.root {
            return;
        }
        let activations = root_owned_activations(world, root, activations.iter().cloned());
        for spec in &self.specs {
            let text = match spec.kind {
                DumpKind::Types => render_types_dump(world, &activations),
                DumpKind::Activations => render_activations_dump(world, &activations),
                _ => continue,
            };
            write_dump_file(&spec.path, &text);
        }
    }

    fn program(&mut self, world: &World, root: RootId) {
        if root != self.root {
            return;
        }
        for spec in &self.specs {
            let text = match spec.kind {
                DumpKind::Backend => format!("{:#?}\n", world.backend_program(root)),
                DumpKind::Native => format!("{:#?}\n", world.native_program(root)),
                DumpKind::Fnir => format!("{:#?}\n", world.native_program(root).module),
                _ => continue,
            };
            write_dump_file(&spec.path, &text);
        }
    }

    fn clif(
        &mut self,
        module: &crate::fz_ir::Module,
        fn_id: crate::fz_ir::FnId,
        function: &cranelift_codegen::ir::Function,
    ) {
        for spec in self.specs.iter().filter(|spec| spec.kind == DumpKind::Clif) {
            if !self.clif_cleared {
                clear_dump_file(&spec.path);
            }
            append_dump_file(
                &spec.path,
                &format!(
                    "; fn {} ({})\n{}\n",
                    module.fn_by_id(fn_id).name,
                    fn_id.0,
                    function.display()
                ),
            );
        }
        self.clif_cleared = true;
    }
}

fn parse_dump_kind_name(name: &str) -> Result<DumpKind, String> {
    match name {
        "activations" | "acts" => Ok(DumpKind::Activations),
        "types" => Ok(DumpKind::Types),
        "backend" => Ok(DumpKind::Backend),
        "native" => Ok(DumpKind::Native),
        "fnir" => Ok(DumpKind::Fnir),
        "clif" => Ok(DumpKind::Clif),
        other => Err(format!(
            "unsupported dump kind `{other}`; expected one of activations, types, backend, native, fnir, clif"
        )),
    }
}

fn render_types_dump(world: &World, activations: &[ActivationKey]) -> String {
    let mut activations = activations.to_vec();
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

fn render_activations_dump(world: &World, activations: &[ActivationKey]) -> String {
    let mut activations = activations.to_vec();
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

/// Filters an activation stream to the root's own code unit (the top-level
/// functions defined alongside the root entry) and deduplicates it. The
/// product inventory yields one entry per demanded executable, so several
/// executables may share an activation; the dump lists each activation once.
fn root_owned_activations(
    world: &World,
    root: RootId,
    activations: impl IntoIterator<Item = ActivationKey>,
) -> Vec<ActivationKey> {
    let root_code = world.function_definition(world.root_function(root)).0.code;
    let mut seen = std::collections::HashSet::new();
    activations
        .into_iter()
        .filter(|activation| world.function_definition(activation.function).0.code == root_code)
        .filter(|activation| seen.insert(activation.clone()))
        .collect()
}

fn render_callsite_summary(world: &World, summary: &super::semantic::CallSiteSummary) -> String {
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

fn activation_sort_key(world: &World, activation: &ActivationKey) -> (String, Vec<String>) {
    (
        function_label(world, activation.function),
        activation
            .inputs(world.types())
            .iter()
            .map(|ty| world.types().display(ty))
            .collect(),
    )
}

fn executable_sort_key(world: &World, executable: &ExecutableKey) -> (String, Vec<String>, String) {
    (
        function_label(world, executable.activation.function),
        executable
            .activation
            .inputs(world.types())
            .iter()
            .map(|ty| world.types().display(ty))
            .collect(),
        format!("{:?}", executable.need),
    )
}

fn activation_label(world: &World, activation: &ActivationKey) -> String {
    let inputs = activation
        .inputs(world.types())
        .iter()
        .map(|ty| world.types().display(ty))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{}[{}]", function_label(world, activation.function), inputs)
}

fn executable_label(world: &World, executable: &ExecutableKey) -> String {
    format!(
        "{} need={:?}",
        activation_label(world, &executable.activation),
        executable.need
    )
}

fn function_label(world: &World, function: FunctionId) -> String {
    let function_ref = world.function_ref(function);
    let module = world.module_name(function_ref.module).unwrap_or_default();
    if module.is_empty() {
        format!("{}/{}", function_ref.name, function_ref.arity)
    } else {
        format!("{}.{}/{}", module, function_ref.name, function_ref.arity)
    }
}

fn span_label(span: crate::source::Span) -> String {
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
