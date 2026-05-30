//! Built-in runtime library modules as separate-compilation inputs.
//!
//! The language runtime has two layers:
//!
//! - primitive extern contracts implemented by Rust/C runtime symbols;
//! - ordinary FZ modules, such as `Utf8` and `Process`, implemented in
//!   per-module source files and consumed through module interfaces.
//!
//! This module exposes the second layer as deterministic `.fzi`/`.fzo`
//! artifact envelopes so resolver and linker work can depend on the same
//! facts a user library would provide.
use crate::ast::{Attribute, Item, ModuleDef, Program};
use crate::modules::artifact::{FziArtifact, FzoArtifact, FzoUnitPayload};
use crate::modules::identity::{ExportKey, ModuleName};
use crate::modules::interface::ModuleInterface;
#[cfg(test)]
use crate::resolve::InterfaceTable;
use std::collections::BTreeMap;
#[cfg(test)]
use std::rc::Rc;

const RUNTIME_PRELUDE_FZ: &str = include_str!("runtime_library/runtime.fz");

struct RuntimeModuleSource {
    name: &'static str,
    source: &'static str,
    role: RuntimeModuleRole,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RuntimeModuleRole {
    CorePrelude,
    Library,
}

const RUNTIME_MODULE_SOURCES: &[RuntimeModuleSource] = &[
    RuntimeModuleSource {
        name: "Kernel",
        source: include_str!("runtime_library/kernel.fz"),
        role: RuntimeModuleRole::CorePrelude,
    },
    RuntimeModuleSource {
        name: "Process",
        source: include_str!("runtime_library/process.fz"),
        role: RuntimeModuleRole::Library,
    },
    RuntimeModuleSource {
        name: "Enum",
        source: include_str!("runtime_library/enum.fz"),
        role: RuntimeModuleRole::Library,
    },
    RuntimeModuleSource {
        name: "Enumerable",
        source: include_str!("runtime_library/enumerable.fz"),
        role: RuntimeModuleRole::Library,
    },
    RuntimeModuleSource {
        name: "Utf8",
        source: include_str!("runtime_library/utf8.fz"),
        role: RuntimeModuleRole::Library,
    },
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RuntimeLibraryModuleArtifact {
    pub module: ModuleName,
    pub interface: ModuleInterface,
    pub fzi: FziArtifact,
    pub fzo: FzoArtifact,
}

pub struct RuntimeRootTypes {
    pub env: crate::type_expr::ModuleTypeEnv,
    pub opaque_inners: crate::type_expr::OpaqueInnerTypes,
    pub brand_inners: crate::type_expr::BrandInnerTypes,
}

pub fn prelude_source() -> &'static str {
    RUNTIME_PRELUDE_FZ
}

pub fn root_type_env<T: crate::types::Types<Ty = crate::types::Ty>>(t: &mut T) -> RuntimeRootTypes {
    let toks = crate::lexer::Lexer::new(prelude_source())
        .tokenize()
        .expect("runtime.fz lex error (bug in built-in prelude)");
    let (_items, attrs) = crate::parser::Parser::new(toks)
        .parse_prelude()
        .expect("runtime.fz parse error (bug in built-in prelude)");
    root_type_env_from_attrs(t, &attrs)
}

pub fn root_type_env_from_attrs<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    attrs: &[Attribute],
) -> RuntimeRootTypes {
    let builtin_env = crate::type_expr::builtin_type_env(t);
    let (env, declared_opaque_inners, declared_brand_inners) =
        crate::type_expr::build_module_type_env_for_with_base(t, attrs, "", &builtin_env)
            .expect("runtime.fz @type error (bug in built-in prelude)");
    let mut opaque_inners = crate::type_expr::builtin_opaque_inners(t);
    opaque_inners.extend(declared_opaque_inners);
    let mut brand_inners = crate::type_expr::builtin_brand_inners(t);
    brand_inners.extend(declared_brand_inners);
    RuntimeRootTypes {
        env,
        opaque_inners,
        brand_inners,
    }
}

pub fn core_prelude_module_sources() -> impl Iterator<Item = (&'static str, &'static str)> {
    RUNTIME_MODULE_SOURCES
        .iter()
        .filter(|source| source.role == RuntimeModuleRole::CorePrelude)
        .map(|source| (source.name, source.source))
}

pub fn is_core_prelude_module(module: &ModuleName) -> bool {
    RUNTIME_MODULE_SOURCES.iter().any(|source| {
        source.role == RuntimeModuleRole::CorePrelude && source.name == module.dotted()
    })
}

pub fn prelude_required_modules() -> Vec<ModuleName> {
    let core_modules = RUNTIME_MODULE_SOURCES
        .iter()
        .filter(|source| source.role == RuntimeModuleRole::CorePrelude)
        .map(|source| ModuleName::from_segments(vec![source.name.to_string()]))
        .collect::<std::collections::BTreeSet<_>>();
    primitive_prelude_program()
        .items
        .iter()
        .filter_map(|item| match &**item {
            Item::Import { path, .. } if !core_modules.contains(path) => Some(path.clone()),
            _ => None,
        })
        .collect()
}

pub fn parsed_program() -> Program {
    let mut items = Vec::new();
    for module_source in RUNTIME_MODULE_SOURCES {
        let toks = crate::lexer::Lexer::new(module_source.source)
            .tokenize()
            .unwrap_or_else(|_| {
                panic!(
                    "{}.fz lex error (bug in built-in runtime library)",
                    module_source.name
                )
            });
        let (mut parsed_items, _attrs) = crate::parser::Parser::new(toks)
            .parse_prelude()
            .unwrap_or_else(|_| {
                panic!(
                    "{}.fz parse error (bug in built-in runtime library)",
                    module_source.name
                )
            });
        items.append(&mut parsed_items);
    }
    Program {
        items,
        module_interfaces: BTreeMap::new(),
        external_module_interfaces: BTreeMap::new(),
        module_docs: Default::default(),
        module_type_envs: Default::default(),
        protocol_registry: Default::default(),
        opaque_inners: Default::default(),
        brand_inners: Default::default(),
    }
}

#[cfg(test)]
pub fn interface_table() -> InterfaceTable {
    RUNTIME_MODULE_SOURCES
        .iter()
        .filter_map(|source| {
            let module = ModuleName::from_segments(vec![source.name.to_string()]);
            interface(&module).map(|interface| (module, interface))
        })
        .collect()
}

pub fn interface(module: &ModuleName) -> Option<ModuleInterface> {
    artifact(module).map(|artifact| artifact.interface)
}

pub fn artifact(module: &ModuleName) -> Option<RuntimeLibraryModuleArtifact> {
    artifacts()
        .into_iter()
        .find(|artifact| artifact.module == *module)
}

pub fn artifacts() -> Vec<RuntimeLibraryModuleArtifact> {
    let prog = parsed_program();
    let interfaces = crate::modules::interface::collect_from_program(&prog);
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
    let unit_payload = FzoUnitPayload::runtime_module(
        runtime_module_source(name).expect("runtime module source is registered"),
    );
    let implementation_fingerprint_digest = crate::modules::artifact::payload_digest(&unit_payload);
    FzoArtifact {
        compiler_abi_version: crate::modules::artifact::FZ_ARTIFACT_ABI_VERSION,
        runtime_abi_version: crate::modules::artifact::FZ_RUNTIME_ARTIFACT_ABI_VERSION,
        module: Some(name.clone()),
        unit_payload,
        required_imports: interface_imports(interface),
        implementation_fingerprint: runtime_implementation_fingerprint(name, module),
        implementation_fingerprint_digest,
        interface_fingerprint_digest: crate::modules::interface::fingerprint_digest(
            &interface_fingerprint,
        ),
        interface_fingerprint,
    }
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

fn runtime_module_source(name: &ModuleName) -> Option<&'static str> {
    RUNTIME_MODULE_SOURCES
        .iter()
        .find(|source| source.name == name.dotted())
        .map(|source| source.source)
}

pub fn primitive_prelude_program() -> Program {
    let toks = crate::lexer::Lexer::new(RUNTIME_PRELUDE_FZ)
        .tokenize()
        .expect("runtime.fz lex error (bug in built-in prelude)");
    let (items, _attrs) = crate::parser::Parser::new(toks)
        .parse_prelude()
        .expect("runtime.fz parse error (bug in built-in prelude)");
    Program {
        items,
        module_interfaces: BTreeMap::new(),
        external_module_interfaces: BTreeMap::new(),
        module_docs: Default::default(),
        module_type_envs: Default::default(),
        protocol_registry: Default::default(),
        opaque_inners: Default::default(),
        brand_inners: Default::default(),
    }
}

#[cfg(test)]
pub fn primitive_contract_names() -> Vec<String> {
    let mut names = Vec::new();
    collect_primitive_contract_names(&primitive_prelude_program().items, &mut names);
    for module in parsed_program().items {
        if let Item::Module(module) = &*module {
            collect_primitive_contract_names(&module.items, &mut names);
        }
    }
    names.sort();
    names
}

#[cfg(test)]
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

        let enumerable = interfaces
            .get(&ModuleName::from_segments(vec!["Enumerable".to_string()]))
            .expect("Enumerable interface");
        assert!(
            enumerable
                .protocols
                .iter()
                .any(|protocol| protocol.name.dotted() == "Enumerable")
        );
        assert!(enumerable.protocol_impls.iter().any(
            |protocol_impl| protocol_impl.protocol.dotted() == "Enumerable"
                && protocol_impl.target.display_name() == "Enumerable.List"
        ));
        assert!(
            !enumerable
                .protocols
                .iter()
                .any(|protocol| protocol.name.dotted() == "Enumerable.Enumerable")
        );

        let enum_module = interfaces
            .get(&ModuleName::from_segments(vec!["Enum".to_string()]))
            .expect("Enum interface");
        let enum_exports = enum_module
            .exports
            .iter()
            .map(|f| format!("{}/{}", f.name, f.arity))
            .collect::<Vec<_>>();
        assert_eq!(
            enum_exports,
            vec![
                "count/1",
                "member?/2",
                "reduce/3",
                "slice/1",
                "sort/1",
                "sort/2"
            ]
        );
        assert!(
            enum_module
                .imports
                .iter()
                .any(|import| import.module.dotted() == "Enumerable")
        );

        assert_eq!(
            utf8.docs.as_deref(),
            Some("UTF-8 validation and branding for byte-aligned binaries.")
        );
        let specs = utf8
            .exports
            .iter()
            .map(|export| {
                let spec = export.spec.as_ref().expect("runtime export spec");
                (
                    format!("{}/{}", export.name, export.arity),
                    spec.params.clone(),
                    spec.result.clone(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            specs,
            vec![
                (
                    "from_bytes/1".to_string(),
                    vec!["Ident(\"binary\")".to_string()],
                    "LBrace Atom(\"ok\") Comma Ident(\"utf8\") RBrace Bar LBrace Atom(\"error\") Comma Atom(\"invalid_utf8\") RBrace".to_string(),
                ),
                (
                    "from_bytes!/1".to_string(),
                    vec!["Ident(\"binary\")".to_string()],
                    "Ident(\"utf8\")".to_string(),
                ),
                (
                    "to_bytes/1".to_string(),
                    vec!["Ident(\"utf8\")".to_string()],
                    "Ident(\"binary\")".to_string(),
                ),
                (
                    "valid?/1".to_string(),
                    vec!["Ident(\"binary\")".to_string()],
                    "Ident(\"bool\")".to_string(),
                ),
            ]
        );

        assert_eq!(
            primitive_contract_names(),
            vec![
                "fz_bitstring_valid_utf8/1",
                "fz_brand_bitstring_as_utf8/1",
                "fz_dbg_value/1",
                "fz_make_ref/0",
                "fz_make_resource/2",
                "fz_panic/1",
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
            let fzi = FziArtifact::deserialize(
                &crate::telemetry::NullTelemetry,
                None,
                &fzi_text,
                Some(&artifact.interface.fingerprint_inputs),
            )
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
            let fzo = FzoArtifact::deserialize(
                &crate::telemetry::NullTelemetry,
                None,
                &fzo_text,
                Some(&artifact.fzo.interface_fingerprint),
            )
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
        let store = crate::modules::artifact_store::ArtifactStore::new(&root);
        let tel = crate::telemetry::ConfiguredTelemetry::new();
        let capture = crate::telemetry::Capture::new();
        tel.attach(&["fz", "module"], capture.handler());
        let artifacts = artifacts();
        let interfaces = artifacts
            .iter()
            .map(|artifact| (artifact.module.clone(), artifact.interface.clone()))
            .collect::<BTreeMap<_, _>>();

        let fzi_paths = store
            .write_fzi_artifacts(&tel, &interfaces)
            .expect("write fzi");
        let fzo_paths = store
            .write_fzo_artifacts(&tel, artifacts.iter().map(|artifact| &artifact.fzo))
            .expect("write fzo");
        assert_eq!(fzi_paths.len(), artifacts.len());
        assert_eq!(fzo_paths.len(), artifacts.len());

        let utf8 = ModuleName::from_segments(vec!["Utf8".to_string()]);
        let loaded_interfaces = store.load_interface_table(&tel, [&utf8]).expect("load fzi");
        assert!(loaded_interfaces[&utf8].exports.iter().any(|export| {
            export.name == "valid?" && export.arity == 1 && export.spec.is_some()
        }));
        let loaded_fzo = store
            .load_fzo_artifact(
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
    fn primitive_prelude_imports_kernel_without_defmodule_body() {
        let prelude = primitive_prelude_program();
        assert!(
            prelude
                .items
                .iter()
                .all(|item| !matches!(&**item, Item::Module(_)))
        );
        assert!(
            prelude.items.iter().any(
                |item| matches!(&**item, Item::Import { path, .. } if path.dotted() == "Kernel")
            )
        );
    }
}
