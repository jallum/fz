//! Deterministic `.fzi` / `.fzo` artifact envelopes for module-first builds.

use crate::diag::source_map::PortableSourceFile;
use crate::diag::{Diagnostic, Span, codes, emit_through};
#[cfg(test)]
use crate::diag::{Diagnostics, SourceMap};
use crate::fz_ir::Module;
#[cfg(test)]
use crate::fz_ir::{CallsiteId, CallsiteIdent, EmitSlot, ExternalCallEdge, FnBuilder, FnId, Term, Var};
use crate::ir_codegen::CompiledUnit;
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::{FZ_INTERFACE_ABI_VERSION, ModuleInterface, fingerprint_digest};
#[cfg(test)]
use crate::modules::interface::{
    InterfaceFn, InterfaceImport, InterfaceImportFn, InterfaceSpec, InterfaceType, InterfaceTypeKind,
};
use crate::telemetry::Telemetry;
#[cfg(test)]
use crate::telemetry::{Capture, ConfiguredTelemetry, Value};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use std::error::Error;
use std::fmt::{Display, Formatter};
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
    pub module: Module,
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

    pub fn emit(&self, tel: &dyn Telemetry, path: Option<&Path>) {
        let mut diagnostic = self.to_diagnostic();
        if let Some(path) = path {
            diagnostic = diagnostic.with_note(format!("artifact path: {}", path.display()));
        }
        emit_through(tel, None, &[diagnostic]);
    }
}

impl Display for ArtifactFormatError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

impl Error for ArtifactFormatError {}

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
        tel: &dyn Telemetry,
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
        Self::from_unit_payload(unit, FzoUnitPayload::source_unit(source), implementation_fingerprint)
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
        Self::from_unit_payload(unit, FzoUnitPayload::ir_unit(body), implementation_fingerprint)
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

    pub fn source_unit_text(&self, tel: &dyn Telemetry) -> Result<&str, ArtifactFormatError> {
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
        tel: &dyn Telemetry,
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
            return emit_invalid(tel, path, "fzo implemented interface fingerprint digest mismatch");
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
    serde_json::from_str(body).map_err(|err| invalid(format!("malformed {} artifact: {}", magic, err)))
}

fn invalid(message: impl Into<String>) -> ArtifactFormatError {
    ArtifactFormatError::new(message)
}

fn emit_invalid<T>(
    tel: &dyn Telemetry,
    path: Option<&Path>,
    message: impl Into<String>,
) -> Result<T, ArtifactFormatError> {
    let err = invalid(message);
    err.emit(tel, path);
    Err(err)
}

#[cfg(test)]
#[path = "artifact_test.rs"]
mod artifact_test;
