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
            specs: vec![InterfaceSpec {
                params: vec!["int".to_string(), "int".to_string()],
                result: "int".to_string(),
            }],
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
        &crate::telemetry::ConfiguredTelemetry::new(),
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
    let err = FziArtifact::deserialize(&crate::telemetry::ConfiguredTelemetry::new(), None, &text, None).unwrap_err();
    assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
    assert_eq!(err.to_string(), "fzi interface fingerprint digest mismatch");
}

#[test]
fn fzi_decode_error_emits_diagnostic_telemetry() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&["fz", "diag"], capture.handler());

    let err = FziArtifact::deserialize(&tel, None, "not-an-artifact", None).unwrap_err();

    assert_eq!(err.to_string(), "expected fzi artifact header");
    assert_eq!(capture.count(&["fz", "diag", "error"]), 1);
    let event = capture.last(&["fz", "diag", "error"]).expect("diag event");
    assert!(matches!(
        event.metadata.get("code"),
        Some(Value::Str(code)) if code == "artifact/invalid"
    ));
    assert!(matches!(
        event.metadata.get("message"),
        Some(Value::Str(message)) if message == "expected fzi artifact header"
    ));
}

#[test]
fn fzo_roundtrip_is_deterministic() {
    let interface = math_interface();
    let mut builder = FnBuilder::new(FnId(0), "Math.add");
    let entry = builder.block(Vec::new());
    builder.set_terminator(entry, Term::Halt(Var(0)));
    let mut code = Module::new();
    code.fn_idx.insert(FnId(0), 0);
    code.fns.push(builder.build());
    code.external_call_edges.push(ExternalCallEdge {
        callsite: CallsiteId {
            caller: FnId(0),
            ident: CallsiteIdent::synthetic(),
            slot: EmitSlot::Direct,
        },
        target: ExportKey::new(module("Dep"), "seed", 0),
    });
    let unit = CompiledUnit::from_ir_module(code, Some(interface.clone()), Diagnostics::new());
    // This module's spans are all synthetic, so it references no source
    // files: an empty `sources` is the faithful structural payload.
    let artifact = FzoArtifact::from_unit_ir(&unit, vec![], vec!["impl:abc".to_string()]);
    let text = artifact.serialize();
    assert!(text.contains(r#""format": "fz-ir-unit-v1""#), "{text}");
    assert!(text.contains(r#""body": "#), "{text}");
    let decoded = FzoArtifact::deserialize(
        &crate::telemetry::ConfiguredTelemetry::new(),
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
    let mut builder = FnBuilder::new(FnId(0), "Math.add");
    let entry = builder.block(Vec::new());
    builder.set_terminator(entry, Term::Halt(Var(0)));
    let mut code = Module::new();
    code.fn_idx.insert(FnId(0), 0);
    code.fns.push(builder.build());
    code.external_call_edges.push(ExternalCallEdge {
        callsite: CallsiteId {
            caller: FnId(0),
            ident: CallsiteIdent::synthetic(),
            slot: EmitSlot::Direct,
        },
        target: ExportKey::new(module("Dep"), "seed", 0),
    });
    let unit = CompiledUnit::from_ir_module(code, Some(interface), Diagnostics::new());

    // The realistic path: intern the unit's source into a SourceMap and
    // pull `to_portable()` for each referenced file. This module's spans are
    // all synthetic, so we add one file and carry it explicitly.
    let mut sm = SourceMap::new();
    let fid = sm.add_file("Math.fz", "defmodule Math do\n  fn add(x, y), do: x + y\nend\n");
    let sources = vec![sm.file(fid).to_portable(fid)];

    let fzo = FzoArtifact::from_unit_ir(&unit, sources.clone(), vec![]);
    let text = fzo.serialize();
    assert!(text.contains(r#""format": "fz-ir-unit-v1""#), "{text}");

    let back = FzoArtifact::deserialize(&crate::telemetry::ConfiguredTelemetry::new(), None, &text, None).unwrap();
    let payload = back.ir_unit_payload().unwrap();

    // The Module survived: canonical Value equality.
    assert_eq!(
        serde_json::to_value(&payload.module).unwrap(),
        serde_json::to_value(&unit.code).unwrap(),
        "module survives the IR-unit round-trip"
    );
    // Sources survived: file id + name + bytes all preserved.
    assert_eq!(payload.sources, sources, "source files survive the round-trip");
}

/// Build a non-trivial structural IR-unit artifact: one fn, one external
/// call edge, one interned source file.
fn structural_ir_artifact() -> FzoArtifact {
    let interface = math_interface();
    let mut builder = FnBuilder::new(FnId(0), "Math.add");
    let entry = builder.block(Vec::new());
    builder.set_terminator(entry, Term::Halt(Var(0)));
    let mut code = Module::new();
    code.fn_idx.insert(FnId(0), 0);
    code.fns.push(builder.build());
    code.external_call_edges.push(ExternalCallEdge {
        callsite: CallsiteId {
            caller: FnId(0),
            ident: CallsiteIdent::synthetic(),
            slot: EmitSlot::Direct,
        },
        target: ExportKey::new(module("Dep"), "seed", 0),
    });
    let unit = CompiledUnit::from_ir_module(code, Some(interface), Diagnostics::new());
    let mut sm = SourceMap::new();
    let fid = sm.add_file("Math.fz", "defmodule Math do\n  fn add(x, y), do: x + y\nend\n");
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
    let decoded = FzoArtifact::deserialize(&crate::telemetry::ConfiguredTelemetry::new(), None, &text, None)
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
        module: Module::new(),
        sources: Vec::new(),
    })
    .expect("tampered payload serialization");
    assert_ne!(artifact.unit_payload.body, tampered_body);
    // Stale digest: mutate the body but NOT implementation_fingerprint_digest.
    artifact.unit_payload.body = tampered_body;
    let text = artifact.serialize();
    // The tampered body is still valid JSON, so this only trips the digest.
    let err = FzoArtifact::deserialize(&crate::telemetry::ConfiguredTelemetry::new(), None, &text, None).unwrap_err();
    assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
    assert_eq!(err.to_string(), "fzo implementation payload digest mismatch");
}

#[test]
fn fzo_ir_unit_payload_rejects_non_ir_unit() {
    let interface = math_interface();
    let unit = CompiledUnit::from_ir_module(Module::new(), Some(interface), Diagnostics::new());
    let artifact = FzoArtifact::from_unit_source(&unit, "defmodule Math do\nend\n", Vec::new());
    let err = artifact.ir_unit_payload().unwrap_err();
    assert_eq!(err.to_string(), "fzo payload `fz-source-unit-v1` is not an IR unit");
}

#[test]
fn fzo_source_unit_payload_is_materializable() {
    let interface = math_interface();
    let unit = CompiledUnit::from_ir_module(Module::new(), Some(interface.clone()), Diagnostics::new());
    let artifact = FzoArtifact::from_unit_source(
        &unit,
        "defmodule Math do\n  fn add(x, y), do: x + y\nend\n",
        vec!["impl:source".to_string()],
    );

    let decoded = FzoArtifact::deserialize(
        &crate::telemetry::ConfiguredTelemetry::new(),
        None,
        &artifact.serialize(),
        Some(&interface.fingerprint_inputs),
    )
    .expect("deserialize");

    assert_eq!(decoded.unit_payload.format, FZO_PAYLOAD_SOURCE_UNIT_V1);
    assert!(
        decoded
            .source_unit_text(&crate::telemetry::ConfiguredTelemetry::new())
            .unwrap()
            .contains("defmodule Math")
    );
}

#[test]
fn fzo_rejects_non_source_payload_as_materializable_source() {
    let interface = math_interface();
    let unit = CompiledUnit::from_ir_module(Module::new(), Some(interface), Diagnostics::new());
    let artifact = FzoArtifact::from_unit_ir(&unit, vec![], Vec::new());

    let err = artifact
        .source_unit_text(&crate::telemetry::ConfiguredTelemetry::new())
        .unwrap_err();

    assert_eq!(
        err.to_string(),
        "fzo payload `fz-ir-unit-v1` is not a materializable source unit"
    );
}

#[test]
fn fzo_rejects_interface_fingerprint_digest_mismatch() {
    let interface = math_interface();
    let unit = CompiledUnit::from_ir_module(Module::new(), Some(interface), Diagnostics::new());
    let artifact = FzoArtifact::from_unit_ir(&unit, vec![], Vec::new());
    let text = artifact
        .serialize()
        .replace(&artifact.interface_fingerprint_digest, "bad");
    let err = FzoArtifact::deserialize(&crate::telemetry::ConfiguredTelemetry::new(), None, &text, None).unwrap_err();
    assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
    assert_eq!(err.to_string(), "fzo implemented interface fingerprint digest mismatch");
}

#[test]
fn fzo_rejects_empty_unit_payload() {
    let interface = math_interface();
    let unit = CompiledUnit::from_ir_module(Module::new(), Some(interface), Diagnostics::new());
    let mut artifact = FzoArtifact::from_unit_ir(&unit, vec![], Vec::new());
    artifact.unit_payload.body.clear();
    let text = artifact.serialize();
    let err = FzoArtifact::deserialize(&crate::telemetry::ConfiguredTelemetry::new(), None, &text, None).unwrap_err();
    assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
    assert_eq!(err.to_string(), "fzo unit payload is empty");
}

#[test]
fn fzo_rejects_interface_fingerprint_mismatch() {
    let interface = math_interface();
    let unit = CompiledUnit::from_ir_module(Module::new(), Some(interface), Diagnostics::new());
    let text = FzoArtifact::from_unit_ir(&unit, vec![], Vec::new()).serialize();
    let err = FzoArtifact::deserialize(
        &crate::telemetry::ConfiguredTelemetry::new(),
        None,
        &text,
        Some(&["wrong".to_string()]),
    )
    .unwrap_err();
    assert_eq!(err.to_diagnostic().code, codes::ARTIFACT_INVALID);
    assert_eq!(err.to_string(), "fzo implemented interface fingerprint mismatch");
}
