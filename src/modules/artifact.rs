//! Deterministic `.fzi` / `.fzo` artifact envelopes for module-first builds.
#![allow(clippy::result_large_err)]

use crate::diag::{Diagnostic, Span, codes};
use crate::ir_codegen::{CompiledUnit, RuntimeUnitMetadata};
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{
    FZ_INTERFACE_ABI_VERSION, InterfaceFn, InterfaceImport, InterfaceImportFn, InterfaceSpec,
    InterfaceType, InterfaceTypeKind, ModuleInterface, fingerprint_digest,
};

pub const FZ_ARTIFACT_ABI_VERSION: u32 = 1;
pub const FZ_RUNTIME_ARTIFACT_ABI_VERSION: u32 = 1;
#[cfg(test)]
pub const FZO_PAYLOAD_IR_TEXT_V1: &str = "fz-ir-text-v1";
pub const FZO_PAYLOAD_SOURCE_UNIT_V1: &str = "fz-source-unit-v1";
pub const FZO_PAYLOAD_RUNTIME_MODULE_V1: &str = "fz-runtime-module-v1";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FziArtifact {
    pub compiler_abi_version: u32,
    pub runtime_abi_version: u32,
    pub interface_fingerprint_digest: String,
    pub interface_fingerprint: Vec<String>,
    pub interface: ModuleInterface,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FzoArtifact {
    pub compiler_abi_version: u32,
    pub runtime_abi_version: u32,
    pub module: Option<ModuleName>,
    pub unit_payload: FzoUnitPayload,
    pub code_fn_count: usize,
    pub required_imports: Vec<ExportKey>,
    pub exported_symbols: Vec<(String, u32)>,
    pub atom_count: usize,
    pub schema_count: usize,
    pub frame_sizes: Vec<u32>,
    pub implementation_fingerprint: Vec<String>,
    pub interface_fingerprint_digest: String,
    pub interface_fingerprint: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FzoUnitPayload {
    pub format: String,
    pub body: String,
}

impl FzoUnitPayload {
    pub fn new(format: impl Into<String>, body: impl Into<String>) -> Self {
        Self {
            format: format.into(),
            body: body.into(),
        }
    }

    #[cfg(test)]
    pub fn ir_text(body: impl Into<String>) -> Self {
        Self::new(FZO_PAYLOAD_IR_TEXT_V1, body)
    }

    pub fn source_unit(body: impl Into<String>) -> Self {
        Self::new(FZO_PAYLOAD_SOURCE_UNIT_V1, body)
    }

    pub fn runtime_module(body: impl Into<String>) -> Self {
        Self::new(FZO_PAYLOAD_RUNTIME_MODULE_V1, body)
    }
}

impl FziArtifact {
    pub fn new(interface: ModuleInterface) -> Self {
        let interface_fingerprint = interface.fingerprint_inputs.clone();
        Self {
            compiler_abi_version: FZ_ARTIFACT_ABI_VERSION,
            runtime_abi_version: FZ_RUNTIME_ARTIFACT_ABI_VERSION,
            interface_fingerprint_digest: fingerprint_digest(&interface_fingerprint),
            interface_fingerprint,
            interface,
        }
    }

    pub fn serialize(&self) -> String {
        let mut lines = Vec::new();
        lines.push("fzi".to_string());
        lines.push(format!("compiler_abi={}", self.compiler_abi_version));
        lines.push(format!("runtime_abi={}", self.runtime_abi_version));
        lines.push(format!("module={}", self.interface.name));
        lines.push(format!("interface_abi={}", self.interface.abi_version));
        lines.push(format!(
            "fingerprint_digest={}",
            self.interface_fingerprint_digest
        ));
        lines.push(format!(
            "docs={}",
            self.interface
                .docs
                .as_deref()
                .map(escape)
                .unwrap_or_default()
        ));
        push_list(&mut lines, "fingerprint", &self.interface_fingerprint);
        lines.push(format!("imports={}", self.interface.imports.len()));
        for import in &self.interface.imports {
            lines.push(format!(
                "import\t{}\t{}\t{}",
                import.module,
                render_import_fns(&import.only),
                render_import_fns(&import.except)
            ));
        }
        lines.push(format!("types={}", self.interface.types.len()));
        for ty in &self.interface.types {
            lines.push(format!(
                "type\t{}\t{}\t{}",
                escape(&ty.name),
                render_type_kind(ty.kind),
                escape(&ty.body)
            ));
        }
        lines.push(format!("exports={}", self.interface.exports.len()));
        for export in &self.interface.exports {
            lines.push(format!(
                "export\t{}\t{}\t{}",
                escape(&export.name),
                export.arity,
                render_spec(export.spec.as_ref())
            ));
        }
        finish(lines)
    }

    pub fn deserialize(
        text: &str,
        expected_fingerprint: Option<&[String]>,
    ) -> Result<Self, Diagnostic> {
        let lines: Vec<&str> = text.lines().collect();
        if lines.first() != Some(&"fzi") {
            return Err(invalid("expected fzi artifact header"));
        }
        let compiler_abi = parse_u32(kv(&lines, "compiler_abi")?)?;
        if compiler_abi != FZ_ARTIFACT_ABI_VERSION {
            return Err(invalid(format!(
                "fzi compiler ABI {} is not supported by ABI {}",
                compiler_abi, FZ_ARTIFACT_ABI_VERSION
            )));
        }
        let runtime_abi = parse_u32(kv(&lines, "runtime_abi")?)?;
        if runtime_abi != FZ_RUNTIME_ARTIFACT_ABI_VERSION {
            return Err(invalid(format!(
                "fzi runtime ABI {} is not supported by ABI {}",
                runtime_abi, FZ_RUNTIME_ARTIFACT_ABI_VERSION
            )));
        }
        let name = module(kv(&lines, "module")?);
        let interface_abi = parse_u32(kv(&lines, "interface_abi")?)?;
        if interface_abi != FZ_INTERFACE_ABI_VERSION {
            return Err(invalid(format!(
                "interface ABI {} is not supported by ABI {}",
                interface_abi, FZ_INTERFACE_ABI_VERSION
            )));
        }
        let docs = unescape(kv(&lines, "docs")?);
        let docs = if docs.is_empty() { None } else { Some(docs) };
        let digest = kv(&lines, "fingerprint_digest")?.to_string();
        let fingerprint = parse_list(&lines, "fingerprint")?;
        let computed_digest = fingerprint_digest(&fingerprint);
        if digest != computed_digest {
            return Err(invalid("fzi interface fingerprint digest mismatch"));
        }
        if let Some(expected) = expected_fingerprint
            && fingerprint != expected
        {
            return Err(invalid("fzi interface fingerprint mismatch"));
        }
        let imports = parse_imports(&lines)?;
        let types = parse_types(&lines)?;
        let exports = parse_exports(&lines)?;
        Ok(Self {
            compiler_abi_version: compiler_abi,
            runtime_abi_version: runtime_abi,
            interface_fingerprint_digest: digest,
            interface_fingerprint: fingerprint.clone(),
            interface: ModuleInterface {
                name,
                abi_version: interface_abi,
                imports,
                exports,
                types,
                docs,
                fingerprint_inputs: fingerprint,
            },
        })
    }
}

impl FzoArtifact {
    #[cfg(test)]
    pub fn from_unit(
        unit: &CompiledUnit,
        runtime: &RuntimeUnitMetadata,
        implementation_fingerprint: Vec<String>,
    ) -> Self {
        Self::from_unit_payload(
            unit,
            runtime,
            FzoUnitPayload::ir_text(unit.code.to_string()),
            implementation_fingerprint,
        )
    }

    pub fn from_unit_source(
        unit: &CompiledUnit,
        runtime: &RuntimeUnitMetadata,
        source: impl Into<String>,
        implementation_fingerprint: Vec<String>,
    ) -> Self {
        Self::from_unit_payload(
            unit,
            runtime,
            FzoUnitPayload::source_unit(source),
            implementation_fingerprint,
        )
    }

    fn from_unit_payload(
        unit: &CompiledUnit,
        runtime: &RuntimeUnitMetadata,
        unit_payload: FzoUnitPayload,
        implementation_fingerprint: Vec<String>,
    ) -> Self {
        let interface_fingerprint = unit.interface_fingerprint.clone();
        Self {
            compiler_abi_version: FZ_ARTIFACT_ABI_VERSION,
            runtime_abi_version: FZ_RUNTIME_ARTIFACT_ABI_VERSION,
            module: unit.module.clone(),
            unit_payload,
            code_fn_count: unit.code.fns.len(),
            required_imports: runtime.imported_refs.clone(),
            exported_symbols: runtime
                .exported_symbols
                .iter()
                .map(|(name, id)| (name.clone(), *id))
                .collect(),
            atom_count: runtime.atoms.len(),
            schema_count: runtime.schemas.len(),
            frame_sizes: runtime.frame_sizes.clone(),
            implementation_fingerprint,
            interface_fingerprint_digest: fingerprint_digest(&interface_fingerprint),
            interface_fingerprint,
        }
    }

    pub fn source_unit_text(&self) -> Result<&str, Diagnostic> {
        if self.unit_payload.format == FZO_PAYLOAD_SOURCE_UNIT_V1 {
            Ok(&self.unit_payload.body)
        } else {
            Err(invalid(format!(
                "fzo payload `{}` is not a materializable source unit",
                self.unit_payload.format
            )))
        }
    }

    pub fn serialize(&self) -> String {
        let mut lines = Vec::new();
        lines.push("fzo".to_string());
        lines.push(format!("compiler_abi={}", self.compiler_abi_version));
        lines.push(format!("runtime_abi={}", self.runtime_abi_version));
        lines.push(format!(
            "module={}",
            self.module
                .as_ref()
                .map(ToString::to_string)
                .unwrap_or_default()
        ));
        lines.push(format!(
            "unit_payload_format={}",
            escape(&self.unit_payload.format)
        ));
        lines.push(format!("unit_payload={}", escape(&self.unit_payload.body)));
        lines.push(format!("code_fn_count={}", self.code_fn_count));
        push_list(
            &mut lines,
            "implementation_fingerprint",
            &self.implementation_fingerprint,
        );
        lines.push(format!(
            "interface_fingerprint_digest={}",
            self.interface_fingerprint_digest
        ));
        push_list(
            &mut lines,
            "interface_fingerprint",
            &self.interface_fingerprint,
        );
        lines.push(format!("imports={}", self.required_imports.len()));
        for import in &self.required_imports {
            lines.push(format!("import\t{}", import));
        }
        lines.push(format!("exports={}", self.exported_symbols.len()));
        for (name, id) in &self.exported_symbols {
            lines.push(format!("export\t{}\t{}", escape(name), id));
        }
        lines.push(format!("atom_count={}", self.atom_count));
        lines.push(format!("schema_count={}", self.schema_count));
        lines.push(format!(
            "frame_sizes={}",
            self.frame_sizes
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(",")
        ));
        finish(lines)
    }

    pub fn deserialize(
        text: &str,
        expected_interface_fingerprint: Option<&[String]>,
    ) -> Result<Self, Diagnostic> {
        let lines: Vec<&str> = text.lines().collect();
        if lines.first() != Some(&"fzo") {
            return Err(invalid("expected fzo artifact header"));
        }
        let compiler_abi = parse_u32(kv(&lines, "compiler_abi")?)?;
        if compiler_abi != FZ_ARTIFACT_ABI_VERSION {
            return Err(invalid("fzo compiler ABI mismatch"));
        }
        let runtime_abi = parse_u32(kv(&lines, "runtime_abi")?)?;
        if runtime_abi != FZ_RUNTIME_ARTIFACT_ABI_VERSION {
            return Err(invalid("fzo runtime ABI mismatch"));
        }
        let module_text = kv(&lines, "module")?;
        let module = if module_text.is_empty() {
            None
        } else {
            Some(module(module_text))
        };
        let unit_payload = FzoUnitPayload::new(
            unescape(kv(&lines, "unit_payload_format")?),
            unescape(kv(&lines, "unit_payload")?),
        );
        if unit_payload.format.is_empty() {
            return Err(invalid("fzo unit payload format is empty"));
        }
        if unit_payload.body.is_empty() {
            return Err(invalid("fzo unit payload is empty"));
        }
        let interface_fingerprint_digest = kv(&lines, "interface_fingerprint_digest")?.to_string();
        let interface_fingerprint = parse_list(&lines, "interface_fingerprint")?;
        let computed_digest = fingerprint_digest(&interface_fingerprint);
        if interface_fingerprint_digest != computed_digest {
            return Err(invalid(
                "fzo implemented interface fingerprint digest mismatch",
            ));
        }
        if let Some(expected) = expected_interface_fingerprint
            && interface_fingerprint != expected
        {
            return Err(invalid("fzo implemented interface fingerprint mismatch"));
        }
        Ok(Self {
            compiler_abi_version: compiler_abi,
            runtime_abi_version: runtime_abi,
            module,
            unit_payload,
            code_fn_count: parse_usize(kv(&lines, "code_fn_count")?)?,
            required_imports: parse_fzo_imports(&lines)?,
            exported_symbols: parse_fzo_exports(&lines)?,
            atom_count: parse_usize(kv(&lines, "atom_count")?)?,
            schema_count: parse_usize(kv(&lines, "schema_count")?)?,
            frame_sizes: parse_u32_csv(kv(&lines, "frame_sizes")?)?,
            implementation_fingerprint: parse_list(&lines, "implementation_fingerprint")?,
            interface_fingerprint_digest,
            interface_fingerprint,
        })
    }
}

fn finish(mut lines: Vec<String>) -> String {
    lines.push(String::new());
    lines.join("\n")
}

fn push_list(lines: &mut Vec<String>, name: &str, values: &[String]) {
    lines.push(format!("{}={}", name, values.len()));
    for value in values {
        lines.push(format!("{}\t{}", name, escape(value)));
    }
}

fn kv<'a>(lines: &'a [&str], key: &str) -> Result<&'a str, Diagnostic> {
    let prefix = format!("{}=", key);
    lines
        .iter()
        .find_map(|line| line.strip_prefix(&prefix))
        .ok_or_else(|| invalid(format!("missing `{}`", key)))
}

fn parse_list(lines: &[&str], name: &str) -> Result<Vec<String>, Diagnostic> {
    let count = parse_usize(kv(lines, name)?)?;
    let prefix = format!("{}\t", name);
    let values: Vec<String> = lines
        .iter()
        .filter_map(|line| line.strip_prefix(&prefix).map(unescape))
        .collect();
    if values.len() != count {
        return Err(invalid(format!("{} count mismatch", name)));
    }
    Ok(values)
}

fn parse_imports(lines: &[&str]) -> Result<Vec<InterfaceImport>, Diagnostic> {
    let count = parse_usize(kv(lines, "imports")?)?;
    let values: Vec<InterfaceImport> = lines
        .iter()
        .filter_map(|line| line.strip_prefix("import\t"))
        .map(|body| {
            let parts: Vec<&str> = body.split('\t').collect();
            if parts.len() != 3 {
                return Err(invalid("malformed import"));
            }
            Ok(InterfaceImport {
                module: module(parts[0]),
                only: parse_import_fns(parts[1])?,
                except: parse_import_fns(parts[2])?,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != count {
        return Err(invalid("imports count mismatch"));
    }
    Ok(values)
}

fn parse_types(lines: &[&str]) -> Result<Vec<InterfaceType>, Diagnostic> {
    let count = parse_usize(kv(lines, "types")?)?;
    let values: Vec<InterfaceType> = lines
        .iter()
        .filter_map(|line| line.strip_prefix("type\t"))
        .map(|body| {
            let parts: Vec<&str> = body.split('\t').collect();
            if parts.len() != 3 {
                return Err(invalid("malformed type"));
            }
            Ok(InterfaceType {
                name: unescape(parts[0]),
                kind: parse_type_kind(parts[1])?,
                body: unescape(parts[2]),
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != count {
        return Err(invalid("types count mismatch"));
    }
    Ok(values)
}

fn parse_exports(lines: &[&str]) -> Result<Vec<InterfaceFn>, Diagnostic> {
    let count = parse_usize(kv(lines, "exports")?)?;
    let values: Vec<InterfaceFn> = lines
        .iter()
        .filter_map(|line| line.strip_prefix("export\t"))
        .map(|body| {
            let parts: Vec<&str> = body.split('\t').collect();
            if parts.len() != 3 {
                return Err(invalid("malformed export"));
            }
            Ok(InterfaceFn {
                name: unescape(parts[0]),
                arity: parse_usize(parts[1])?,
                spec: parse_spec(parts[2])?,
                name_span: Span::DUMMY,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != count {
        return Err(invalid("exports count mismatch"));
    }
    Ok(values)
}

fn parse_fzo_imports(lines: &[&str]) -> Result<Vec<ExportKey>, Diagnostic> {
    let count = parse_usize(kv(lines, "imports")?)?;
    let values: Vec<ExportKey> = lines
        .iter()
        .filter_map(|line| line.strip_prefix("import\t"))
        .map(parse_export_key)
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != count {
        return Err(invalid("fzo imports count mismatch"));
    }
    Ok(values)
}

fn parse_fzo_exports(lines: &[&str]) -> Result<Vec<(String, u32)>, Diagnostic> {
    let count = parse_usize(kv(lines, "exports")?)?;
    let values: Vec<(String, u32)> = lines
        .iter()
        .filter_map(|line| line.strip_prefix("export\t"))
        .map(|body| {
            let parts: Vec<&str> = body.split('\t').collect();
            if parts.len() != 2 {
                return Err(invalid("malformed fzo export"));
            }
            Ok((unescape(parts[0]), parse_u32(parts[1])?))
        })
        .collect::<Result<Vec<_>, _>>()?;
    if values.len() != count {
        return Err(invalid("fzo exports count mismatch"));
    }
    Ok(values)
}

fn render_import_fns(fns: &[InterfaceImportFn]) -> String {
    fns.iter()
        .map(|f| format!("{}/{}", escape(&f.name), f.arity))
        .collect::<Vec<_>>()
        .join(",")
}

fn parse_import_fns(text: &str) -> Result<Vec<InterfaceImportFn>, Diagnostic> {
    if text.is_empty() {
        return Ok(Vec::new());
    }
    text.split(',')
        .map(|part| {
            let Some((name, arity)) = part.rsplit_once('/') else {
                return Err(invalid("malformed import function"));
            };
            Ok(InterfaceImportFn {
                name: unescape(name),
                arity: parse_usize(arity)?,
            })
        })
        .collect()
}

fn render_spec(spec: Option<&InterfaceSpec>) -> String {
    match spec {
        Some(spec) => format!(
            "{}=>{}",
            spec.params
                .iter()
                .map(|s| escape(s))
                .collect::<Vec<_>>()
                .join(","),
            escape(&spec.result)
        ),
        None => String::new(),
    }
}

fn parse_spec(text: &str) -> Result<Option<InterfaceSpec>, Diagnostic> {
    if text.is_empty() {
        return Ok(None);
    }
    let Some((params, result)) = text.split_once("=>") else {
        return Err(invalid("malformed spec"));
    };
    Ok(Some(InterfaceSpec {
        params: if params.is_empty() {
            Vec::new()
        } else {
            params.split(',').map(unescape).collect()
        },
        result: unescape(result),
    }))
}

fn render_type_kind(kind: InterfaceTypeKind) -> &'static str {
    match kind {
        InterfaceTypeKind::Alias => "alias",
        InterfaceTypeKind::Opaque => "opaque",
        InterfaceTypeKind::Refines => "refines",
    }
}

fn parse_type_kind(text: &str) -> Result<InterfaceTypeKind, Diagnostic> {
    match text {
        "alias" => Ok(InterfaceTypeKind::Alias),
        "opaque" => Ok(InterfaceTypeKind::Opaque),
        "refines" => Ok(InterfaceTypeKind::Refines),
        _ => Err(invalid("unknown type kind")),
    }
}

fn parse_export_key(text: &str) -> Result<ExportKey, Diagnostic> {
    let Some((qualified, arity)) = text.rsplit_once('/') else {
        return Err(invalid("malformed export key"));
    };
    let Some((module_name, name)) = qualified.rsplit_once('.') else {
        return Err(invalid("malformed export key"));
    };
    Ok(ExportKey::new(
        module(module_name),
        name,
        parse_usize(arity)?,
    ))
}

fn module(text: &str) -> ModuleName {
    ModuleName::from_segments(text.split('.').map(str::to_string).collect())
}

fn parse_usize(text: &str) -> Result<usize, Diagnostic> {
    text.parse::<usize>()
        .map_err(|_| invalid(format!("expected usize, got `{}`", text)))
}

fn parse_u32(text: &str) -> Result<u32, Diagnostic> {
    text.parse::<u32>()
        .map_err(|_| invalid(format!("expected u32, got `{}`", text)))
}

fn parse_u32_csv(text: &str) -> Result<Vec<u32>, Diagnostic> {
    if text.is_empty() {
        return Ok(Vec::new());
    }
    text.split(',').map(parse_u32).collect()
}

fn escape(text: &str) -> String {
    text.replace('\\', "\\\\")
        .replace('\t', "\\t")
        .replace('\n', "\\n")
}

fn unescape(text: &str) -> String {
    let mut out = String::new();
    let mut chars = text.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('t') => out.push('\t'),
                Some('\\') => out.push('\\'),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(ch);
        }
    }
    out
}

fn invalid(message: impl Into<String>) -> Diagnostic {
    Diagnostic::error(codes::ARTIFACT_INVALID, message.into(), Span::DUMMY)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir_codegen::{CompiledUnit, RuntimeEntrypoints, RuntimeUnitMetadata};
    use fz_runtime::heap::Schema;
    use std::collections::BTreeMap;

    fn math_interface() -> ModuleInterface {
        ModuleInterface {
            name: module("Math"),
            abi_version: FZ_INTERFACE_ABI_VERSION,
            imports: vec![InterfaceImport {
                module: module("Dep"),
                only: vec![InterfaceImportFn {
                    name: "seed".to_string(),
                    arity: 0,
                }],
                except: Vec::new(),
            }],
            exports: vec![InterfaceFn {
                name: "add".to_string(),
                arity: 2,
                spec: Some(InterfaceSpec {
                    params: vec!["int".to_string(), "int".to_string()],
                    result: "int".to_string(),
                }),
                name_span: Span::DUMMY,
            }],
            types: vec![InterfaceType {
                name: "id".to_string(),
                kind: InterfaceTypeKind::Alias,
                body: "int".to_string(),
            }],
            docs: Some("math docs".to_string()),
            fingerprint_inputs: vec!["export:Math.add/2".to_string()],
        }
    }

    #[test]
    fn fzi_roundtrip_is_deterministic() {
        let artifact = FziArtifact::new(math_interface());
        let text = artifact.serialize();
        let decoded = FziArtifact::deserialize(&text, Some(&["export:Math.add/2".to_string()]))
            .expect("deserialize");
        assert_eq!(decoded, artifact);
        assert_eq!(decoded.serialize(), text);
    }

    #[test]
    fn fzi_rejects_fingerprint_mismatch() {
        let text = FziArtifact::new(math_interface()).serialize();
        let err = FziArtifact::deserialize(&text, Some(&["different".to_string()])).unwrap_err();
        assert_eq!(err.code, codes::ARTIFACT_INVALID);
        assert_eq!(err.message, "fzi interface fingerprint mismatch");
    }

    #[test]
    fn fzi_rejects_fingerprint_digest_mismatch() {
        let text = FziArtifact::new(math_interface())
            .serialize()
            .replace("fingerprint_digest=", "fingerprint_digest=bad");
        let err = FziArtifact::deserialize(&text, None).unwrap_err();
        assert_eq!(err.code, codes::ARTIFACT_INVALID);
        assert_eq!(err.message, "fzi interface fingerprint digest mismatch");
    }

    #[test]
    fn fzo_roundtrip_is_deterministic() {
        let interface = math_interface();
        let mut builder = crate::fz_ir::FnBuilder::new(crate::fz_ir::FnId(0), "Math.add");
        let entry = builder.block(Vec::new());
        builder.set_terminator(entry, crate::fz_ir::Term::Halt(crate::fz_ir::Var(0)));
        let mut code = crate::fz_ir::Module::new();
        code.fn_idx.insert(crate::fz_ir::FnId(0), 0);
        code.fns.push(builder.build());
        let unit = CompiledUnit::from_ir_module(
            code,
            Some(interface.clone()),
            crate::diag::Diagnostics::new(),
        );
        let runtime = RuntimeUnitMetadata {
            module: Some(interface.name.clone()),
            atoms: vec!["ok".to_string()],
            schemas: vec![Schema::tuple_of_arity(2)],
            frame_sizes: vec![16],
            exported_symbols: BTreeMap::from([("Math.add/2".to_string(), 0)]),
            imported_refs: vec![ExportKey::new(module("Dep"), "seed", 0)],
            static_closures: Vec::new(),
            halt_kinds: BTreeMap::new(),
            entrypoints: RuntimeEntrypoints::default(),
        };
        let expected_payload = unit.code.to_string();
        let artifact = FzoArtifact::from_unit(&unit, &runtime, vec!["impl:abc".to_string()]);
        let text = artifact.serialize();
        assert!(text.contains("unit_payload_format=fz-ir-text-v1"), "{text}");
        assert!(text.contains("unit_payload="), "{text}");
        let decoded = FzoArtifact::deserialize(&text, Some(&["export:Math.add/2".to_string()]))
            .expect("deserialize");
        assert_eq!(decoded.unit_payload.format, "fz-ir-text-v1");
        assert_eq!(decoded.unit_payload.body, expected_payload);
        assert_eq!(decoded, artifact);
        assert_eq!(decoded.serialize(), text);
    }

    #[test]
    fn fzo_source_unit_payload_is_materializable() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface.clone()),
            crate::diag::Diagnostics::new(),
        );
        let runtime = RuntimeUnitMetadata::from_ir_module(None, &unit.code);
        let artifact = FzoArtifact::from_unit_source(
            &unit,
            &runtime,
            "defmodule Math do\n  fn add(x, y), do: x + y\nend\n",
            vec!["impl:source".to_string()],
        );

        let decoded =
            FzoArtifact::deserialize(&artifact.serialize(), Some(&interface.fingerprint_inputs))
                .expect("deserialize");

        assert_eq!(decoded.unit_payload.format, FZO_PAYLOAD_SOURCE_UNIT_V1);
        assert!(
            decoded
                .source_unit_text()
                .unwrap()
                .contains("defmodule Math")
        );
    }

    #[test]
    fn fzo_rejects_non_source_payload_as_materializable_source() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface),
            crate::diag::Diagnostics::new(),
        );
        let runtime = RuntimeUnitMetadata::from_ir_module(None, &unit.code);
        let artifact = FzoArtifact::from_unit(&unit, &runtime, Vec::new());

        let err = artifact.source_unit_text().unwrap_err();

        assert_eq!(
            err.message,
            "fzo payload `fz-ir-text-v1` is not a materializable source unit"
        );
    }

    #[test]
    fn fzo_rejects_interface_fingerprint_digest_mismatch() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface),
            crate::diag::Diagnostics::new(),
        );
        let runtime = RuntimeUnitMetadata::from_ir_module(None, &unit.code);
        let text = FzoArtifact::from_unit(&unit, &runtime, Vec::new())
            .serialize()
            .replace(
                "interface_fingerprint_digest=",
                "interface_fingerprint_digest=bad",
            );
        let err = FzoArtifact::deserialize(&text, None).unwrap_err();
        assert_eq!(err.code, codes::ARTIFACT_INVALID);
        assert_eq!(
            err.message,
            "fzo implemented interface fingerprint digest mismatch"
        );
    }

    #[test]
    fn fzo_rejects_missing_unit_payload() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface),
            crate::diag::Diagnostics::new(),
        );
        let runtime = RuntimeUnitMetadata::from_ir_module(None, &unit.code);
        let text = FzoArtifact::from_unit(&unit, &runtime, Vec::new())
            .serialize()
            .replace("unit_payload=", "unit_payload");
        let err = FzoArtifact::deserialize(&text, None).unwrap_err();
        assert_eq!(err.code, codes::ARTIFACT_INVALID);
        assert_eq!(err.message, "missing `unit_payload`");
    }

    #[test]
    fn fzo_rejects_interface_fingerprint_mismatch() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface),
            crate::diag::Diagnostics::new(),
        );
        let runtime = RuntimeUnitMetadata::from_ir_module(None, &unit.code);
        let text = FzoArtifact::from_unit(&unit, &runtime, Vec::new()).serialize();
        let err = FzoArtifact::deserialize(&text, Some(&["wrong".to_string()])).unwrap_err();
        assert_eq!(err.code, codes::ARTIFACT_INVALID);
        assert_eq!(
            err.message,
            "fzo implemented interface fingerprint mismatch"
        );
    }
}
