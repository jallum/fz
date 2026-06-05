use super::*;

#[test]
fn module_name_builds_from_segments_without_parsing_display_text() {
    let name = ModuleName::from_segments(vec!["Outer".into(), "Inner".into()]);
    assert_eq!(name.segments(), &["Outer".to_string(), "Inner".to_string()]);
    assert_eq!(name.dotted(), "Outer.Inner");
    assert_eq!(name.child("Leaf").dotted(), "Outer.Inner.Leaf");
}

#[test]
fn module_name_parses_dotted_display_spelling_at_edges() {
    let name = ModuleName::parse_dotted("Outer.Inner").expect("parse module name");
    assert_eq!(name.segments(), &["Outer".to_string(), "Inner".to_string()]);
    assert!(ModuleName::parse_dotted("").is_err());
    assert!(ModuleName::parse_dotted("Outer..Inner").is_err());
}

#[test]
fn export_key_names_module_function_and_arity() {
    let key = ExportKey::new(ModuleName::from_segments(vec!["Math".into()]), "add", 2);
    assert_eq!(key.to_string(), "Math.add/2");
}

#[test]
fn mfa_names_top_level_and_module_qualified_functions() {
    let top = Mfa::top_level("main", 0);
    assert_eq!(top.qualified_name(), "main");
    assert_eq!(top.to_string(), "main/0");
    assert!(top.module().is_none());

    let nested = Mfa::from_qualified("Outer.Inner.run", 2);
    assert_eq!(nested.module().expect("qualified module").dotted(), "Outer.Inner");
    assert_eq!(nested.qualified.name, "run");
    assert_eq!(nested.qualified_name(), "Outer.Inner.run");
    assert_eq!(nested.to_string(), "Outer.Inner.run/2");
}
