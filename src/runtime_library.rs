//! Built-in runtime library modules as separate-compilation inputs.
//!
//! The language runtime has two layers:
//!
//! - primitive extern contracts implemented by Rust/C runtime symbols;
//! - ordinary FZ modules, such as `Utf8` and `Process`, implemented in
//!   `runtime.fz` and consumed through module interfaces.
//!
//! This module exposes the second layer as deterministic `.fzi`/`.fzo`
//! artifact envelopes so resolver and linker work can depend on the same
//! facts a user library would provide.
#![allow(dead_code)]

use crate::ast::{Item, ModuleDef, Program};
use crate::diag::Span;
use crate::module_artifact::{FziArtifact, FzoArtifact, FzoUnitPayload};
use crate::module_identity::{ExportKey, ModuleName};
use crate::module_interface::ModuleInterface;
use crate::resolve::InterfaceTable;
use std::collections::BTreeMap;
use std::rc::Rc;

const RUNTIME_FZ: &str = include_str!("runtime_library/runtime.fz");

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeLibraryModuleArtifact {
    pub module: ModuleName,
    pub interface: ModuleInterface,
    pub fzi: FziArtifact,
    pub fzo: FzoArtifact,
}

pub fn source() -> &'static str {
    RUNTIME_FZ
}

pub fn parsed_program() -> Program {
    let toks = crate::lexer::Lexer::new(RUNTIME_FZ)
        .tokenize()
        .expect("runtime.fz lex error (bug in built-in runtime library)");
    let (items, _attrs) = crate::parser::Parser::new(toks)
        .parse_prelude()
        .expect("runtime.fz parse error (bug in built-in runtime library)");
    Program {
        items,
        module_interfaces: BTreeMap::new(),
        module_docs: Default::default(),
        module_type_envs: Default::default(),
        opaque_inners: Default::default(),
        brand_inners: Default::default(),
    }
}

pub fn interface_table() -> InterfaceTable {
    crate::module_interface::collect_from_program(&parsed_program())
}

pub fn artifacts() -> Vec<RuntimeLibraryModuleArtifact> {
    let prog = parsed_program();
    let interfaces = crate::module_interface::collect_from_program(&prog);
    let mut out = Vec::new();
    for item in &prog.items {
        if let Item::Module(module) = &**item {
            collect_artifacts_recursive(module, None, &interfaces, &mut out);
        }
    }
    out
}

fn collect_artifacts_recursive(
    module: &ModuleDef,
    parent: Option<&ModuleName>,
    interfaces: &BTreeMap<ModuleName, ModuleInterface>,
    out: &mut Vec<RuntimeLibraryModuleArtifact>,
) {
    let name = if let Some(parent) = parent {
        parent.child(module.name.clone())
    } else {
        ModuleName::from_segments(vec![module.name.clone()])
    };
    if let Some(interface) = interfaces.get(&name) {
        let fzi = FziArtifact::new(interface.clone());
        let fzo = runtime_module_fzo(module, &name, interface);
        out.push(RuntimeLibraryModuleArtifact {
            module: name.clone(),
            interface: interface.clone(),
            fzi,
            fzo,
        });
    }
    for item in &module.items {
        if let Item::Module(inner) = &**item {
            collect_artifacts_recursive(inner, Some(&name), interfaces, out);
        }
    }
}

fn runtime_module_fzo(
    module: &ModuleDef,
    name: &ModuleName,
    interface: &ModuleInterface,
) -> FzoArtifact {
    let interface_fingerprint = interface.fingerprint_inputs.clone();
    FzoArtifact {
        compiler_abi_version: crate::module_artifact::FZ_ARTIFACT_ABI_VERSION,
        runtime_abi_version: crate::module_artifact::FZ_RUNTIME_ARTIFACT_ABI_VERSION,
        module: Some(name.clone()),
        unit_payload: FzoUnitPayload::runtime_module(runtime_module_payload(name, module)),
        code_fn_count: module_fn_count(module),
        required_imports: interface_imports(interface),
        exported_symbols: interface
            .exports
            .iter()
            .enumerate()
            .map(|(idx, export)| {
                (
                    format!("{}.{}/{}", name, export.name, export.arity),
                    idx as u32,
                )
            })
            .collect(),
        atom_count: 0,
        schema_count: 0,
        frame_sizes: Vec::new(),
        implementation_fingerprint: runtime_implementation_fingerprint(name, module),
        interface_fingerprint_digest: crate::module_interface::fingerprint_digest(
            &interface_fingerprint,
        ),
        interface_fingerprint,
    }
}

fn module_fn_count(module: &ModuleDef) -> usize {
    module
        .items
        .iter()
        .filter(|item| matches!(&***item, Item::Fn(def) if def.extern_abi.is_none()))
        .count()
}

fn interface_imports(interface: &ModuleInterface) -> Vec<ExportKey> {
    interface
        .imports
        .iter()
        .flat_map(|import| {
            import
                .only
                .iter()
                .map(|f| ExportKey::new(import.module.clone(), f.name.clone(), f.arity))
                .collect::<Vec<_>>()
        })
        .collect()
}

fn runtime_implementation_fingerprint(name: &ModuleName, module: &ModuleDef) -> Vec<String> {
    let mut out = vec![
        "kind=runtime-library-module".to_string(),
        format!("module={}", name),
    ];
    for item in &module.items {
        if let Item::Fn(def) = &**item {
            let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
            let kind = if def.extern_abi.is_some() {
                "primitive"
            } else {
                "fz"
            };
            out.push(format!("fn={}/{}:{}", def.name, arity, kind));
        }
    }
    out
}

fn runtime_module_payload(name: &ModuleName, module: &ModuleDef) -> String {
    let mut lines = vec![format!("module={}", name)];
    for item in &module.items {
        if let Item::Fn(def) = &**item
            && def.extern_abi.is_none()
        {
            let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
            lines.push(format!("fn={}/{}", def.name, arity));
        }
    }
    lines.join("\n")
}

pub fn primitive_prelude_program() -> Program {
    let items = parsed_program()
        .items
        .into_iter()
        .filter(|item| !matches!(&**item, Item::Module(_)))
        .collect::<Vec<Rc<Item>>>();
    Program {
        items,
        module_interfaces: BTreeMap::new(),
        module_docs: Default::default(),
        module_type_envs: Default::default(),
        opaque_inners: Default::default(),
        brand_inners: Default::default(),
    }
}

pub fn primitive_contract_names() -> Vec<String> {
    let mut names = Vec::new();
    collect_primitive_contract_names(&parsed_program().items, &mut names);
    names.sort();
    names
}

fn collect_primitive_contract_names(items: &[Rc<Item>], names: &mut Vec<String>) {
    for item in items {
        if let Item::Fn(def) = &**item
            && def.extern_abi.is_some()
        {
            let arity = def.extern_params.len();
            names.push(format!("{}/{}", def.name, arity));
        }
        if let Item::Module(module) = &**item {
            collect_primitive_contract_names(&module.items, names);
        }
    }
}

pub fn module_span_for(name: &ModuleName) -> Span {
    for item in parsed_program().items {
        if let Item::Module(module) = &*item {
            let module_name = ModuleName::from_segments(vec![module.name.clone()]);
            if &module_name == name {
                return module.name_span;
            }
        }
    }
    Span::DUMMY
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_library_interfaces_expose_fz_functions_not_primitive_externs() {
        let interfaces = interface_table();
        let utf8 = interfaces
            .get(&ModuleName::from_segments(vec!["Utf8".to_string()]))
            .expect("Utf8 interface");

        let exports = utf8
            .exports
            .iter()
            .map(|f| format!("{}/{}", f.name, f.arity))
            .collect::<Vec<_>>();
        assert_eq!(
            exports,
            vec!["from_bytes/1", "from_bytes!/1", "to_bytes/1", "valid?/1"]
        );
        assert!(!exports.iter().any(|name| name.starts_with("fz_")));

        assert_eq!(
            primitive_contract_names(),
            vec![
                "fz_assert/1",
                "fz_assert_eq/2",
                "fz_assert_neq/2",
                "fz_bitstring_valid_utf8/1",
                "fz_brand_bitstring_as_utf8/1",
                "fz_make_ref/0",
                "fz_make_resource/2",
                "fz_print_i64/1",
                "fz_print_value/1",
                "fz_process_heap_alloc_stats/0",
                "fz_self/0",
                "fz_send/2",
                "fz_spawn/1",
                "fz_spawn_opt/2",
            ]
        );
    }

    #[test]
    fn runtime_library_artifacts_round_trip_deterministically() {
        let artifacts = artifacts();
        assert!(!artifacts.is_empty());

        for artifact in artifacts {
            let fzi_text = artifact.fzi.serialize();
            let fzi =
                FziArtifact::deserialize(&fzi_text, Some(&artifact.interface.fingerprint_inputs))
                    .expect("fzi roundtrip");
            assert_eq!(fzi.interface.name, artifact.interface.name);
            assert_eq!(fzi.interface.imports, artifact.interface.imports);
            assert_eq!(fzi.interface.types, artifact.interface.types);
            assert_eq!(
                fzi.interface
                    .exports
                    .iter()
                    .map(|f| (&f.name, f.arity, &f.spec))
                    .collect::<Vec<_>>(),
                artifact
                    .interface
                    .exports
                    .iter()
                    .map(|f| (&f.name, f.arity, &f.spec))
                    .collect::<Vec<_>>()
            );

            let fzo_text = artifact.fzo.serialize();
            let fzo =
                FzoArtifact::deserialize(&fzo_text, Some(&artifact.fzo.interface_fingerprint))
                    .expect("fzo roundtrip");
            assert_eq!(fzo.module, Some(artifact.module));
            assert_eq!(
                fzo.interface_fingerprint,
                artifact.interface.fingerprint_inputs
            );
        }
    }

    #[test]
    fn runtime_library_artifacts_write_load_and_import_like_user_artifacts() {
        let root = std::env::temp_dir().join(format!(
            "fz-runtime-artifacts-{}-write-load",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&root);
        let store = crate::module_artifact_store::ArtifactStore::new(&root);
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let capture = crate::telemetry::Capture::new();
        tel.attach(&["fz", "module"], capture.handler());
        let artifacts = artifacts();
        let interfaces = artifacts
            .iter()
            .map(|artifact| (artifact.module.clone(), artifact.interface.clone()))
            .collect::<BTreeMap<_, _>>();

        let fzi_paths = store
            .write_fzi_artifacts_with_telemetry(&tel, &interfaces)
            .expect("write fzi");
        let fzo_paths = store
            .write_fzo_artifacts_with_telemetry(
                &tel,
                artifacts.iter().map(|artifact| &artifact.fzo),
            )
            .expect("write fzo");
        assert_eq!(fzi_paths.len(), artifacts.len());
        assert_eq!(fzo_paths.len(), artifacts.len());

        let utf8 = ModuleName::from_segments(vec!["Utf8".to_string()]);
        let loaded_interfaces = store
            .load_interface_table_with_telemetry(&tel, [&utf8])
            .expect("load fzi");
        assert!(loaded_interfaces[&utf8].exports.iter().any(|export| {
            export.name == "valid?" && export.arity == 1 && export.spec.is_some()
        }));
        let loaded_fzo = store
            .load_fzo_artifact_with_telemetry(
                &tel,
                &utf8,
                Some(&loaded_interfaces[&utf8].fingerprint_inputs),
            )
            .expect("load fzo");
        assert_eq!(loaded_fzo.module, Some(utf8));
        assert_eq!(loaded_fzo.unit_payload.format, "fz-runtime-module-v1");

        let mut t = crate::types::ConcreteTypes;
        let consumer = r#"
defmodule User do
  import Utf8, only: [valid?: 1]
  @spec accepts(any) :: bool
  fn accepts(bytes), do: valid?(bytes)
end
"#;
        match crate::frontend::compile_source_with_interface_table(
            &mut t,
            consumer.to_string(),
            "consumer.fz".to_string(),
            loaded_interfaces,
            &crate::telemetry::NullTelemetry,
        ) {
            Ok(_) => {}
            Err(_) => panic!("runtime artifact interface resolves like a user artifact"),
        }
        assert!(capture.contains(&["fz", "module", "fzi_written"]));
        assert!(capture.contains(&["fz", "module", "fzo_written"]));
        assert!(capture.contains(&["fz", "module", "fzi_loaded"]));
        assert!(capture.contains(&["fz", "module", "fzo_loaded"]));

        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn primitive_prelude_keeps_top_level_contracts_out_of_stdlib_modules() {
        let prelude = primitive_prelude_program();
        assert!(
            prelude
                .items
                .iter()
                .all(|item| !matches!(&**item, Item::Module(_)))
        );
        assert!(
            prelude
                .items
                .iter()
                .any(|item| matches!(&**item, Item::Fn(def) if def.name == "print"))
        );
    }
}
