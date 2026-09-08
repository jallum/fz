use super::CodeMap;

#[test]
fn compiler2_code_text_is_total_for_defined_code() {
    let mut code = CodeMap::new();
    let owner = code.define(Some("main.fz".to_string()), "fn main(), do: 42\n".to_string());
    let version = code.version(owner).expect("submitted source has an immutable version");

    assert_eq!(code.source_map().borrow().name(version), Some("main.fz"));
    assert_eq!(
        code.source_map().borrow().code(version).bytes.as_ref(),
        "fn main(), do: 42\n"
    );
}

#[test]
fn compiler2_reserved_source_owner_does_not_materialize_a_version() {
    let mut code = CodeMap::new();
    let before = code.source_map().borrow().code_count();
    let owner = code.reserve();

    assert_eq!(code.version(owner), None);
    assert_eq!(code.source_map().borrow().code_count(), before);
}
