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
fn mfa_names_compiler_owned_module_and_function_identity() {
    let mfa = Mfa::new(ModuleId(7), "run", 2);
    assert_eq!(mfa.module_id, ModuleId(7));
    assert_eq!(mfa.function_name, "run");
    assert_eq!(mfa.arity, 2);
}
