//! Deterministic `.fzi` / `.fzo` artifact envelopes for module-first builds.

use crate::diag::source_map::PortableSourceFile;
use crate::diag::{Diagnostic, Span, codes};
use crate::ir_codegen::CompiledUnit;
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{FZ_INTERFACE_ABI_VERSION, ModuleInterface, fingerprint_digest};
#[cfg(test)]
use crate::modules::interface::{
    InterfaceFn, InterfaceImport, InterfaceImportFn, InterfaceSpec, InterfaceType,
    InterfaceTypeKind,
};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use std::path::Path;

pub const FZ_ARTIFACT_ABI_VERSION: u32 = 1;
pub const FZ_RUNTIME_ARTIFACT_ABI_VERSION: u32 = 1;
pub const FZO_PAYLOAD_SOURCE_UNIT_V1: &str = "fz-source-unit-v1";
pub const FZO_PAYLOAD_RUNTIME_MODULE_V1: &str = "fz-runtime-module-v1";
pub const FZO_PAYLOAD_IR_UNIT_V1: &str = "fz-ir-unit-v1";

const FZI_MAGIC: &str = "fzi";
const FZO_MAGIC: &str = "fzo";

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FziArtifact {
    pub compiler_abi_version: u32,
    pub runtime_abi_version: u32,
    pub interface_fingerprint_digest: String,
    pub interface_fingerprint: Vec<String>,
    pub interface: ModuleInterface,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FzoArtifact {
    pub compiler_abi_version: u32,
    pub runtime_abi_version: u32,
    pub module: Option<ModuleName>,
    pub unit_payload: FzoUnitPayload,
    pub required_imports: Vec<ExportKey>,
    pub implementation_fingerprint: Vec<String>,
    pub implementation_fingerprint_digest: String,
    pub interface_fingerprint_digest: String,
    pub interface_fingerprint: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FzoUnitPayload {
    pub format: String,
    pub body: String,
}

/// Integrity digest over the PAYLOAD CONTENT (format tag + full body). Covers
/// the serialized IR + sources for structural units, or the source text for
/// source units. Recomputed at load to reject semantically-valid-but-tampered
/// payloads that still parse as JSON.
pub(crate) fn payload_digest(payload: &FzoUnitPayload) -> String {
    fingerprint_digest(&[payload.format.clone(), payload.body.clone()])
}

/// Decoded body of an `FZO_PAYLOAD_IR_UNIT_V1` payload: the structural IR
/// `Module` plus every source file its spans reference. A later loader
/// (fz-t1m.3.1.3) re-interns `sources` into the host `SourceMap`, remaps the
/// module's `FileId`s, and materializes the provider WITHOUT recompiling.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IrUnitPayload {
    pub module: crate::fz_ir::Module,
    pub sources: Vec<PortableSourceFile>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactFormatError {
    message: String,
}

impl ArtifactFormatError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    pub fn to_diagnostic(&self) -> Diagnostic {
        Diagnostic::error(codes::ARTIFACT_INVALID, self.message.clone(), Span::DUMMY)
    }

    pub fn emit(&self, tel: &dyn crate::telemetry::Telemetry, path: Option<&Path>) {
        let mut diagnostic = self.to_diagnostic();
        if let Some(path) = path {
            diagnostic = diagnostic.with_note(format!("artifact path: {}", path.display()));
        }
        crate::diag::emit_through(tel, None, &[diagnostic]);
    }
}

impl std::fmt::Display for ArtifactFormatError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for ArtifactFormatError {}

impl FzoUnitPayload {
    pub fn new(format: impl Into<String>, body: impl Into<String>) -> Self {
        Self {
            format: format.into(),
            body: body.into(),
        }
    }

    #[cfg(test)]
    pub fn source_unit(body: impl Into<String>) -> Self {
        Self::new(FZO_PAYLOAD_SOURCE_UNIT_V1, body)
    }

    pub fn runtime_module(body: impl Into<String>) -> Self {
        Self::new(FZO_PAYLOAD_RUNTIME_MODULE_V1, body)
    }

    fn ir_unit(body: impl Into<String>) -> Self {
        Self::new(FZO_PAYLOAD_IR_UNIT_V1, body)
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
        encode(FZI_MAGIC, self)
    }

    pub fn deserialize(
        tel: &dyn crate::telemetry::Telemetry,
        path: Option<&Path>,
        text: &str,
        expected_fingerprint: Option<&[String]>,
    ) -> Result<Self, ArtifactFormatError> {
        let artifact: Self = decode(FZI_MAGIC, text).inspect_err(|err| {
            err.emit(tel, path);
        })?;
        if artifact.compiler_abi_version != FZ_ARTIFACT_ABI_VERSION {
            return emit_invalid(
                tel,
                path,
                format!(
                    "fzi compiler ABI {} is not supported by ABI {}",
                    artifact.compiler_abi_version, FZ_ARTIFACT_ABI_VERSION
                ),
            );
        }
        if artifact.runtime_abi_version != FZ_RUNTIME_ARTIFACT_ABI_VERSION {
            return emit_invalid(
                tel,
                path,
                format!(
                    "fzi runtime ABI {} is not supported by ABI {}",
                    artifact.runtime_abi_version, FZ_RUNTIME_ARTIFACT_ABI_VERSION
                ),
            );
        }
        if artifact.interface.abi_version != FZ_INTERFACE_ABI_VERSION {
            return emit_invalid(
                tel,
                path,
                format!(
                    "interface ABI {} is not supported by ABI {}",
                    artifact.interface.abi_version, FZ_INTERFACE_ABI_VERSION
                ),
            );
        }
        let computed_digest = fingerprint_digest(&artifact.interface_fingerprint);
        if artifact.interface_fingerprint_digest != computed_digest {
            return emit_invalid(tel, path, "fzi interface fingerprint digest mismatch");
        }
        if artifact.interface.fingerprint_inputs != artifact.interface_fingerprint {
            return emit_invalid(tel, path, "fzi interface fingerprint inputs mismatch");
        }
        if let Some(expected) = expected_fingerprint
            && artifact.interface_fingerprint != expected
        {
            return emit_invalid(tel, path, "fzi interface fingerprint mismatch");
        }
        Ok(artifact)
    }
}

impl FzoArtifact {
    #[cfg(test)]
    pub fn from_unit_source(
        unit: &CompiledUnit,
        source: impl Into<String>,
        implementation_fingerprint: Vec<String>,
    ) -> Self {
        Self::from_unit_payload(
            unit,
            FzoUnitPayload::source_unit(source),
            implementation_fingerprint,
        )
    }

    /// Build an `.fzo` whose payload is the STRUCTURAL IR unit: the module's
    /// serde form plus every source file its spans reference, so a later loader
    /// can materialize the provider WITHOUT recompiling. The
    /// `required_imports`/fingerprint wiring is identical to `from_unit_source`.
    /// Production `fz build` emits this structural format; the loader in
    /// `modules::pipeline::load_provider_units` materializes it without the
    /// frontend.
    pub fn from_unit_ir(
        unit: &CompiledUnit,
        sources: Vec<PortableSourceFile>,
        implementation_fingerprint: Vec<String>,
    ) -> Self {
        let body = serde_json::to_string(&IrUnitPayload {
            module: unit.code.clone(),
            sources,
        })
        .expect("ir unit payload serialization");
        Self::from_unit_payload(
            unit,
            FzoUnitPayload::ir_unit(body),
            implementation_fingerprint,
        )
    }

    fn from_unit_payload(
        unit: &CompiledUnit,
        unit_payload: FzoUnitPayload,
        implementation_fingerprint: Vec<String>,
    ) -> Self {
        let interface_fingerprint = unit.interface_fingerprint.clone();
        let implementation_fingerprint_digest = payload_digest(&unit_payload);
        Self {
            compiler_abi_version: FZ_ARTIFACT_ABI_VERSION,
            runtime_abi_version: FZ_RUNTIME_ARTIFACT_ABI_VERSION,
            module: unit.module.clone(),
            unit_payload,
            required_imports: unit
                .code
                .external_call_edges
                .iter()
                .map(|edge| edge.target.clone())
                .collect(),
            implementation_fingerprint,
            implementation_fingerprint_digest,
            interface_fingerprint_digest: fingerprint_digest(&interface_fingerprint),
            interface_fingerprint,
        }
    }

    pub fn source_unit_text(
        &self,
        tel: &dyn crate::telemetry::Telemetry,
    ) -> Result<&str, ArtifactFormatError> {
        if self.unit_payload.format == FZO_PAYLOAD_SOURCE_UNIT_V1
            || self.unit_payload.format == FZO_PAYLOAD_RUNTIME_MODULE_V1
        {
            Ok(&self.unit_payload.body)
        } else {
            emit_invalid(
                tel,
                None,
                format!(
                    "fzo payload `{}` is not a materializable source unit",
                    self.unit_payload.format
                ),
            )
        }
    }

    /// Decode an IR-unit payload back into its `Module` + source files. The
    /// read side `modules::pipeline::load_provider_units` calls to materialize a
    /// provider structurally. Errors if this artifact is not an
    /// `FZO_PAYLOAD_IR_UNIT_V1` unit.
    pub fn ir_unit_payload(&self) -> Result<IrUnitPayload, ArtifactFormatError> {
        if self.unit_payload.format != FZO_PAYLOAD_IR_UNIT_V1 {
            return Err(invalid(format!(
                "fzo payload `{}` is not an IR unit",
                self.unit_payload.format
            )));
        }
        serde_json::from_str(&self.unit_payload.body)
            .map_err(|err| invalid(format!("malformed fzo IR unit payload: {}", err)))
    }

    pub fn serialize(&self) -> String {
        encode(FZO_MAGIC, self)
    }

    pub fn deserialize(
        tel: &dyn crate::telemetry::Telemetry,
        path: Option<&Path>,
        text: &str,
        expected_interface_fingerprint: Option<&[String]>,
    ) -> Result<Self, ArtifactFormatError> {
        let artifact: Self = decode(FZO_MAGIC, text).inspect_err(|err| {
            err.emit(tel, path);
        })?;
        if artifact.compiler_abi_version != FZ_ARTIFACT_ABI_VERSION {
            return emit_invalid(tel, path, "fzo compiler ABI mismatch");
        }
        if artifact.runtime_abi_version != FZ_RUNTIME_ARTIFACT_ABI_VERSION {
            return emit_invalid(tel, path, "fzo runtime ABI mismatch");
        }
        if artifact.unit_payload.format.is_empty() {
            return emit_invalid(tel, path, "fzo unit payload format is empty");
        }
        if artifact.unit_payload.body.is_empty() {
            return emit_invalid(tel, path, "fzo unit payload is empty");
        }
        let computed_digest = fingerprint_digest(&artifact.interface_fingerprint);
        if artifact.interface_fingerprint_digest != computed_digest {
            return emit_invalid(
                tel,
                path,
                "fzo implemented interface fingerprint digest mismatch",
            );
        }
        if let Some(expected) = expected_interface_fingerprint
            && artifact.interface_fingerprint != expected
        {
            return emit_invalid(tel, path, "fzo implemented interface fingerprint mismatch");
        }
        if artifact.implementation_fingerprint_digest != payload_digest(&artifact.unit_payload) {
            return emit_invalid(tel, path, "fzo implementation payload digest mismatch");
        }
        Ok(artifact)
    }
}

fn encode<T: Serialize>(magic: &str, value: &T) -> String {
    let body = serde_json::to_string_pretty(value).expect("artifact serialization should not fail");
    format!("{}\n{}\n", magic, body)
}

fn decode<T: DeserializeOwned>(magic: &str, text: &str) -> Result<T, ArtifactFormatError> {
    let Some((header, body)) = text.split_once('\n') else {
        return Err(invalid(format!("expected {} artifact header", magic)));
    };
    if header != magic {
        return Err(invalid(format!("expected {} artifact header", magic)));
    }
    serde_json::from_str(body)
        .map_err(|err| invalid(format!("malformed {} artifact: {}", magic, err)))
}

fn invalid(message: impl Into<String>) -> ArtifactFormatError {
    ArtifactFormatError::new(message)
}

fn emit_invalid<T>(
    tel: &dyn crate::telemetry::Telemetry,
    path: Option<&Path>,
    message: impl Into<String>,
) -> Result<T, ArtifactFormatError> {
    let err = invalid(message);
    err.emit(tel, path);
    Err(err)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir_codegen::CompiledUnit;

    fn module(text: &str) -> ModuleName {
        ModuleName::parse_dotted(text).expect("test module name")
    }

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
            protocols: Vec::new(),
            protocol_impls: Vec::new(),
            docs: Some("math docs".to_string()),
            fingerprint_inputs: vec!["export:Math.add/2".to_string()],
        }
    }

    #[test]
    fn fzi_roundtrip_is_deterministic() {
        let artifact = FziArtifact::new(math_interface());
        let text = artifact.serialize();
        let decoded = FziArtifact::deserialize(
            &crate::telemetry::NullTelemetry,
            None,
            &text,
            Some(&["export:Math.add/2".to_string()]),
        )
        .expect("deserialize");
        assert_eq!(decoded, artifact);
        assert_eq!(decoded.serialize(), text);
    }

    #[test]
    fn fzi_rejects_fingerprint_mismatch() {
        let text = FziArtifact::new(math_interface()).serialize();
        let err = FziArtifact::deserialize(
            &crate::telemetry::NullTelemetry,
            None,
            &text,
            Some(&["different".to_string()]),
        )
        .unwrap_err();
        assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
        assert_eq!(err.to_string(), "fzi interface fingerprint mismatch");
    }

    #[test]
    fn fzi_rejects_fingerprint_digest_mismatch() {
        let artifact = FziArtifact::new(math_interface());
        let text = artifact
            .serialize()
            .replace(&artifact.interface_fingerprint_digest, "bad");
        let err = FziArtifact::deserialize(&crate::telemetry::NullTelemetry, None, &text, None)
            .unwrap_err();
        assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
        assert_eq!(err.to_string(), "fzi interface fingerprint digest mismatch");
    }

    #[test]
    fn fzi_decode_error_emits_diagnostic_telemetry() {
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let capture = crate::telemetry::Capture::new();
        tel.attach(&["fz", "diag"], capture.handler());

        let err = FziArtifact::deserialize(&tel, None, "not-an-artifact", None).unwrap_err();

        assert_eq!(err.to_string(), "expected fzi artifact header");
        assert_eq!(capture.count(&["fz", "diag", "error"]), 1);
        let event = capture.last(&["fz", "diag", "error"]).expect("diag event");
        assert!(matches!(
            event.metadata.get("code"),
            Some(crate::telemetry::Value::Str(code)) if code == "artifact/invalid"
        ));
        assert!(matches!(
            event.metadata.get("message"),
            Some(crate::telemetry::Value::Str(message)) if message == "expected fzi artifact header"
        ));
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
        code.external_call_edges
            .push(crate::fz_ir::ExternalCallEdge {
                callsite: crate::fz_ir::CallsiteId {
                    caller: crate::fz_ir::FnId(0),
                    ident: crate::fz_ir::CallsiteIdent::synthetic(),
                    slot: crate::fz_ir::EmitSlot::Direct,
                },
                target: ExportKey::new(module("Dep"), "seed", 0),
            });
        let unit = CompiledUnit::from_ir_module(
            code,
            Some(interface.clone()),
            crate::diag::Diagnostics::new(),
        );
        // This module's spans are all synthetic, so it references no source
        // files: an empty `sources` is the faithful structural payload.
        let artifact = FzoArtifact::from_unit_ir(&unit, vec![], vec!["impl:abc".to_string()]);
        let text = artifact.serialize();
        assert!(text.contains(r#""format": "fz-ir-unit-v1""#), "{text}");
        assert!(text.contains(r#""body": "#), "{text}");
        let decoded = FzoArtifact::deserialize(
            &crate::telemetry::NullTelemetry,
            None,
            &text,
            Some(&["export:Math.add/2".to_string()]),
        )
        .expect("deserialize");
        assert_eq!(decoded.unit_payload.format, FZO_PAYLOAD_IR_UNIT_V1);
        assert_eq!(decoded, artifact);
        assert_eq!(decoded.serialize(), text);
    }

    #[test]
    fn fzo_ir_unit_round_trips() {
        // A real unit: one fn, an external call edge — enough that the module's
        // serde form is non-trivial and survives the round-trip unchanged.
        let interface = math_interface();
        let mut builder = crate::fz_ir::FnBuilder::new(crate::fz_ir::FnId(0), "Math.add");
        let entry = builder.block(Vec::new());
        builder.set_terminator(entry, crate::fz_ir::Term::Halt(crate::fz_ir::Var(0)));
        let mut code = crate::fz_ir::Module::new();
        code.fn_idx.insert(crate::fz_ir::FnId(0), 0);
        code.fns.push(builder.build());
        code.external_call_edges
            .push(crate::fz_ir::ExternalCallEdge {
                callsite: crate::fz_ir::CallsiteId {
                    caller: crate::fz_ir::FnId(0),
                    ident: crate::fz_ir::CallsiteIdent::synthetic(),
                    slot: crate::fz_ir::EmitSlot::Direct,
                },
                target: ExportKey::new(module("Dep"), "seed", 0),
            });
        let unit =
            CompiledUnit::from_ir_module(code, Some(interface), crate::diag::Diagnostics::new());

        // The realistic path: intern the unit's source into a SourceMap and
        // pull `to_portable()` for each referenced file. This module's spans are
        // all synthetic, so we add one file and carry it explicitly.
        let mut sm = crate::diag::SourceMap::new();
        let fid = sm.add_file(
            "Math.fz",
            "defmodule Math do\n  fn add(x, y), do: x + y\nend\n",
        );
        let sources = vec![sm.file(fid).to_portable(fid)];

        let fzo = FzoArtifact::from_unit_ir(&unit, sources.clone(), vec![]);
        let text = fzo.serialize();
        assert!(text.contains(r#""format": "fz-ir-unit-v1""#), "{text}");

        let back =
            FzoArtifact::deserialize(&crate::telemetry::NullTelemetry, None, &text, None).unwrap();
        let payload = back.ir_unit_payload().unwrap();

        // The Module survived: canonical Value equality.
        assert_eq!(
            serde_json::to_value(&payload.module).unwrap(),
            serde_json::to_value(&unit.code).unwrap(),
            "module survives the IR-unit round-trip"
        );
        // Sources survived: name + bytes + content_hash all preserved.
        assert_eq!(
            payload.sources, sources,
            "source files survive the round-trip"
        );
    }

    /// Build a non-trivial structural IR-unit artifact: one fn, one external
    /// call edge, one interned source file.
    fn structural_ir_artifact() -> FzoArtifact {
        let interface = math_interface();
        let mut builder = crate::fz_ir::FnBuilder::new(crate::fz_ir::FnId(0), "Math.add");
        let entry = builder.block(Vec::new());
        builder.set_terminator(entry, crate::fz_ir::Term::Halt(crate::fz_ir::Var(0)));
        let mut code = crate::fz_ir::Module::new();
        code.fn_idx.insert(crate::fz_ir::FnId(0), 0);
        code.fns.push(builder.build());
        code.external_call_edges
            .push(crate::fz_ir::ExternalCallEdge {
                callsite: crate::fz_ir::CallsiteId {
                    caller: crate::fz_ir::FnId(0),
                    ident: crate::fz_ir::CallsiteIdent::synthetic(),
                    slot: crate::fz_ir::EmitSlot::Direct,
                },
                target: ExportKey::new(module("Dep"), "seed", 0),
            });
        let unit =
            CompiledUnit::from_ir_module(code, Some(interface), crate::diag::Diagnostics::new());
        let mut sm = crate::diag::SourceMap::new();
        let fid = sm.add_file(
            "Math.fz",
            "defmodule Math do\n  fn add(x, y), do: x + y\nend\n",
        );
        let sources = vec![sm.file(fid).to_portable(fid)];
        FzoArtifact::from_unit_ir(&unit, sources, vec!["impl:struct".to_string()])
    }

    #[test]
    fn fzo_payload_digest_round_trips() {
        let artifact = structural_ir_artifact();
        // The construct path set a digest over format + body.
        assert_eq!(
            artifact.implementation_fingerprint_digest,
            payload_digest(&artifact.unit_payload)
        );
        let text = artifact.serialize();
        let decoded = FzoArtifact::deserialize(&crate::telemetry::NullTelemetry, None, &text, None)
            .expect("matching payload digest is accepted");
        assert_eq!(decoded, artifact);
    }

    #[test]
    fn fzo_rejects_tampered_payload() {
        // Serialize a valid structural artifact, then swap its body for a
        // DIFFERENT-but-valid IrUnitPayload JSON while leaving the stored
        // implementation_fingerprint_digest stale.
        let mut artifact = structural_ir_artifact();
        let tampered_body = serde_json::to_string(&IrUnitPayload {
            module: crate::fz_ir::Module::new(),
            sources: Vec::new(),
        })
        .expect("tampered payload serialization");
        assert_ne!(artifact.unit_payload.body, tampered_body);
        // Stale digest: mutate the body but NOT implementation_fingerprint_digest.
        artifact.unit_payload.body = tampered_body;
        let text = artifact.serialize();
        // The tampered body is still valid JSON, so this only trips the digest.
        let err = FzoArtifact::deserialize(&crate::telemetry::NullTelemetry, None, &text, None)
            .unwrap_err();
        assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
        assert_eq!(
            err.to_string(),
            "fzo implementation payload digest mismatch"
        );
    }

    #[test]
    fn fzo_ir_unit_payload_rejects_non_ir_unit() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface),
            crate::diag::Diagnostics::new(),
        );
        let artifact = FzoArtifact::from_unit_source(&unit, "defmodule Math do\nend\n", Vec::new());
        let err = artifact.ir_unit_payload().unwrap_err();
        assert_eq!(
            err.to_string(),
            "fzo payload `fz-source-unit-v1` is not an IR unit"
        );
    }

    #[test]
    fn fzo_source_unit_payload_is_materializable() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface.clone()),
            crate::diag::Diagnostics::new(),
        );
        let artifact = FzoArtifact::from_unit_source(
            &unit,
            "defmodule Math do\n  fn add(x, y), do: x + y\nend\n",
            vec!["impl:source".to_string()],
        );

        let decoded = FzoArtifact::deserialize(
            &crate::telemetry::NullTelemetry,
            None,
            &artifact.serialize(),
            Some(&interface.fingerprint_inputs),
        )
        .expect("deserialize");

        assert_eq!(decoded.unit_payload.format, FZO_PAYLOAD_SOURCE_UNIT_V1);
        assert!(
            decoded
                .source_unit_text(&crate::telemetry::NullTelemetry)
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
        let artifact = FzoArtifact::from_unit_ir(&unit, vec![], Vec::new());

        let err = artifact
            .source_unit_text(&crate::telemetry::NullTelemetry)
            .unwrap_err();

        assert_eq!(
            err.to_string(),
            "fzo payload `fz-ir-unit-v1` is not a materializable source unit"
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
        let artifact = FzoArtifact::from_unit_ir(&unit, vec![], Vec::new());
        let text = artifact
            .serialize()
            .replace(&artifact.interface_fingerprint_digest, "bad");
        let err = FzoArtifact::deserialize(&crate::telemetry::NullTelemetry, None, &text, None)
            .unwrap_err();
        assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
        assert_eq!(
            err.to_string(),
            "fzo implemented interface fingerprint digest mismatch"
        );
    }

    #[test]
    fn fzo_rejects_empty_unit_payload() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface),
            crate::diag::Diagnostics::new(),
        );
        let mut artifact = FzoArtifact::from_unit_ir(&unit, vec![], Vec::new());
        artifact.unit_payload.body.clear();
        let text = artifact.serialize();
        let err = FzoArtifact::deserialize(&crate::telemetry::NullTelemetry, None, &text, None)
            .unwrap_err();
        assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
        assert_eq!(err.to_string(), "fzo unit payload is empty");
    }

    #[test]
    fn fzo_rejects_interface_fingerprint_mismatch() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface),
            crate::diag::Diagnostics::new(),
        );
        let text = FzoArtifact::from_unit_ir(&unit, vec![], Vec::new()).serialize();
        let err = FzoArtifact::deserialize(
            &crate::telemetry::NullTelemetry,
            None,
            &text,
            Some(&["wrong".to_string()]),
        )
        .unwrap_err();
        assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
        assert_eq!(
            err.to_string(),
            "fzo implemented interface fingerprint mismatch"
        );
    }
}
