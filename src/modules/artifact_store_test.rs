use super::*;
use crate::diag::Span;
use crate::modules::interface::{FZ_INTERFACE_ABI_VERSION, InterfaceFn};
use crate::telemetry::NullTelemetry;
use std::env::temp_dir;
use std::fs::remove_dir_all;
use std::process::id as process_id;

fn module(segments: &[&str]) -> ModuleName {
    ModuleName::from_segments(segments.iter().map(|s| s.to_string()).collect())
}

#[test]
fn default_root_is_build_fz() {
    assert_eq!(ArtifactStore::default_build().root(), Path::new("build/fz"));
}

#[test]
fn top_level_module_paths_are_deterministic() {
    let store = ArtifactStore::new("out");
    let name = module(&["Utf8"]);

    assert_eq!(
        store.interface_path(&name).unwrap(),
        PathBuf::from("out/interfaces/Utf8.fzi")
    );
    assert_eq!(store.object_path(&name).unwrap(), PathBuf::from("out/objects/Utf8.fzo"));
}

#[test]
fn nested_module_paths_preserve_segments() {
    let store = ArtifactStore::new("out");
    let name = module(&["Outer", "Inner"]);

    assert_eq!(
        store.interface_path(&name).unwrap(),
        PathBuf::from("out/interfaces/Outer/Inner.fzi")
    );
    assert_eq!(
        store.object_path(&name).unwrap(),
        PathBuf::from("out/objects/Outer/Inner.fzo")
    );
}

#[test]
fn path_policy_rejects_segments_that_could_escape_root() {
    let store = ArtifactStore::new("out");
    for bad in ["..", ".", "A/B", "A\\B", "A-B", "A B", "A:B"] {
        let err = store.interface_path(&module(&["Outer", bad])).unwrap_err();
        assert_eq!(err.segment(), bad);
    }
}

#[test]
fn writes_and_loads_fzi_artifacts_without_provider_source() {
    let root = temp_dir().join(format!("fz-artifacts-{}-writes-and-loads-fzi", process_id()));
    let _ = remove_dir_all(&root);
    let store = ArtifactStore::new(&root);
    let name = module(&["Provider"]);
    let interface = ModuleInterface {
        name: name.clone(),
        abi_version: FZ_INTERFACE_ABI_VERSION,
        imports: Vec::new(),
        exports: vec![InterfaceFn {
            name: "id".to_string(),
            arity: 1,
            specs: Vec::new(),
            name_span: Span::DUMMY,
        }],
        types: Vec::new(),
        protocols: Vec::new(),
        protocol_impls: Vec::new(),
        docs: None,
        fingerprint_inputs: vec![
            "abi=1".to_string(),
            "module=Provider".to_string(),
            "fn=id/1:<unspecified>".to_string(),
        ],
    };
    let mut interfaces = BTreeMap::new();
    interfaces.insert(name.clone(), interface.clone());

    let written = store.write_fzi_artifacts(&NullTelemetry, &interfaces).unwrap();
    assert_eq!(written, vec![root.join("interfaces/Provider.fzi")]);

    let loaded = store.load_interface_table(&NullTelemetry, [&name]).unwrap();
    assert_eq!(loaded.get(&name), Some(&interface));

    let _ = remove_dir_all(&root);
}
