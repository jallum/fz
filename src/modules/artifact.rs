//! Deterministic `.fzi` / `.fzo` artifact envelopes for module-first builds.
#![allow(clippy::result_large_err)]

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

pub const FZ_ARTIFACT_ABI_VERSION: u32 = 1;
pub const FZ_RUNTIME_ARTIFACT_ABI_VERSION: u32 = 1;
#[cfg(test)]
pub const FZO_PAYLOAD_IR_TEXT_V1: &str = "fz-ir-text-v1";
pub const FZO_PAYLOAD_SOURCE_UNIT_V1: &str = "fz-source-unit-v1";
pub const FZO_PAYLOAD_RUNTIME_MODULE_V1: &str = "fz-runtime-module-v1";

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
    pub interface_fingerprint_digest: String,
    pub interface_fingerprint: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
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
        encode(FZI_MAGIC, self)
    }

    pub fn deserialize(
        text: &str,
        expected_fingerprint: Option<&[String]>,
    ) -> Result<Self, Diagnostic> {
        let artifact: Self = decode(FZI_MAGIC, text)?;
        if artifact.compiler_abi_version != FZ_ARTIFACT_ABI_VERSION {
            return Err(invalid(format!(
                "fzi compiler ABI {} is not supported by ABI {}",
                artifact.compiler_abi_version, FZ_ARTIFACT_ABI_VERSION
            )));
        }
        if artifact.runtime_abi_version != FZ_RUNTIME_ARTIFACT_ABI_VERSION {
            return Err(invalid(format!(
                "fzi runtime ABI {} is not supported by ABI {}",
                artifact.runtime_abi_version, FZ_RUNTIME_ARTIFACT_ABI_VERSION
            )));
        }
        if artifact.interface.abi_version != FZ_INTERFACE_ABI_VERSION {
            return Err(invalid(format!(
                "interface ABI {} is not supported by ABI {}",
                artifact.interface.abi_version, FZ_INTERFACE_ABI_VERSION
            )));
        }
        let computed_digest = fingerprint_digest(&artifact.interface_fingerprint);
        if artifact.interface_fingerprint_digest != computed_digest {
            return Err(invalid("fzi interface fingerprint digest mismatch"));
        }
        if artifact.interface.fingerprint_inputs != artifact.interface_fingerprint {
            return Err(invalid("fzi interface fingerprint inputs mismatch"));
        }
        if let Some(expected) = expected_fingerprint
            && artifact.interface_fingerprint != expected
        {
            return Err(invalid("fzi interface fingerprint mismatch"));
        }
        Ok(artifact)
    }
}

impl FzoArtifact {
    #[cfg(test)]
    pub fn from_unit(unit: &CompiledUnit, implementation_fingerprint: Vec<String>) -> Self {
        Self::from_unit_payload(
            unit,
            FzoUnitPayload::ir_text(unit.code.to_string()),
            implementation_fingerprint,
        )
    }

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

    fn from_unit_payload(
        unit: &CompiledUnit,
        unit_payload: FzoUnitPayload,
        implementation_fingerprint: Vec<String>,
    ) -> Self {
        let interface_fingerprint = unit.interface_fingerprint.clone();
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
            interface_fingerprint_digest: fingerprint_digest(&interface_fingerprint),
            interface_fingerprint,
        }
    }

    pub fn source_unit_text(&self) -> Result<&str, Diagnostic> {
        if self.unit_payload.format == FZO_PAYLOAD_SOURCE_UNIT_V1
            || self.unit_payload.format == FZO_PAYLOAD_RUNTIME_MODULE_V1
        {
            Ok(&self.unit_payload.body)
        } else {
            Err(invalid(format!(
                "fzo payload `{}` is not a materializable source unit",
                self.unit_payload.format
            )))
        }
    }

    pub fn serialize(&self) -> String {
        encode(FZO_MAGIC, self)
    }

    pub fn deserialize(
        text: &str,
        expected_interface_fingerprint: Option<&[String]>,
    ) -> Result<Self, Diagnostic> {
        let artifact: Self = decode(FZO_MAGIC, text)?;
        if artifact.compiler_abi_version != FZ_ARTIFACT_ABI_VERSION {
            return Err(invalid("fzo compiler ABI mismatch"));
        }
        if artifact.runtime_abi_version != FZ_RUNTIME_ARTIFACT_ABI_VERSION {
            return Err(invalid("fzo runtime ABI mismatch"));
        }
        if artifact.unit_payload.format.is_empty() {
            return Err(invalid("fzo unit payload format is empty"));
        }
        if artifact.unit_payload.body.is_empty() {
            return Err(invalid("fzo unit payload is empty"));
        }
        let computed_digest = fingerprint_digest(&artifact.interface_fingerprint);
        if artifact.interface_fingerprint_digest != computed_digest {
            return Err(invalid(
                "fzo implemented interface fingerprint digest mismatch",
            ));
        }
        if let Some(expected) = expected_interface_fingerprint
            && artifact.interface_fingerprint != expected
        {
            return Err(invalid("fzo implemented interface fingerprint mismatch"));
        }
        Ok(artifact)
    }
}

fn encode<T: Serialize>(magic: &str, value: &T) -> String {
    let body = serde_json::to_string_pretty(value).expect("artifact serialization should not fail");
    format!("{}\n{}\n", magic, body)
}

fn decode<T: DeserializeOwned>(magic: &str, text: &str) -> Result<T, Diagnostic> {
    let Some((header, body)) = text.split_once('\n') else {
        return Err(invalid(format!("expected {} artifact header", magic)));
    };
    if header != magic {
        return Err(invalid(format!("expected {} artifact header", magic)));
    }
    serde_json::from_str(body)
        .map_err(|err| invalid(format!("malformed {} artifact: {}", magic, err)))
}

fn invalid(message: impl Into<String>) -> Diagnostic {
    Diagnostic::error(codes::ARTIFACT_INVALID, message.into(), Span::DUMMY)
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
        let artifact = FziArtifact::new(math_interface());
        let text = artifact
            .serialize()
            .replace(&artifact.interface_fingerprint_digest, "bad");
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
        let expected_payload = unit.code.to_string();
        let artifact = FzoArtifact::from_unit(&unit, vec!["impl:abc".to_string()]);
        let text = artifact.serialize();
        assert!(text.contains(r#""format": "fz-ir-text-v1""#), "{text}");
        assert!(text.contains(r#""body": "#), "{text}");
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
        let artifact = FzoArtifact::from_unit_source(
            &unit,
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
        let artifact = FzoArtifact::from_unit(&unit, Vec::new());

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
        let artifact = FzoArtifact::from_unit(&unit, Vec::new());
        let text = artifact
            .serialize()
            .replace(&artifact.interface_fingerprint_digest, "bad");
        let err = FzoArtifact::deserialize(&text, None).unwrap_err();
        assert_eq!(err.code, codes::ARTIFACT_INVALID);
        assert_eq!(
            err.message,
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
        let mut artifact = FzoArtifact::from_unit(&unit, Vec::new());
        artifact.unit_payload.body.clear();
        let text = artifact.serialize();
        let err = FzoArtifact::deserialize(&text, None).unwrap_err();
        assert_eq!(err.code, codes::ARTIFACT_INVALID);
        assert_eq!(err.message, "fzo unit payload is empty");
    }

    #[test]
    fn fzo_rejects_interface_fingerprint_mismatch() {
        let interface = math_interface();
        let unit = CompiledUnit::from_ir_module(
            crate::fz_ir::Module::new(),
            Some(interface),
            crate::diag::Diagnostics::new(),
        );
        let text = FzoArtifact::from_unit(&unit, Vec::new()).serialize();
        let err = FzoArtifact::deserialize(&text, Some(&["wrong".to_string()])).unwrap_err();
        assert_eq!(err.code, codes::ARTIFACT_INVALID);
        assert_eq!(
            err.message,
            "fzo implemented interface fingerprint mismatch"
        );
    }
}
