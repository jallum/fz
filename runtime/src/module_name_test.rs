use super::{ModuleName, alias_spelling, is_alias_namespace_atom};

fn name(segments: &[&str]) -> ModuleName {
    ModuleName::from_segments(segments.iter().map(|s| s.to_string()).collect())
}

#[test]
fn a_module_name_is_the_atom_under_the_elixir_root() {
    assert_eq!(name(&["RuntimeError"]).atom_name(), "Elixir.RuntimeError");
    assert_eq!(name(&["Foo", "Bar"]).atom_name(), "Elixir.Foo.Bar");
}

#[test]
fn every_module_name_atom_prints_back_as_its_alias() {
    for segments in [&["RuntimeError"][..], &["Foo", "Bar"], &["Foo_9", "B2"]] {
        let module = name(segments);
        assert_eq!(alias_spelling(&module.atom_name()), Some(module.dotted().as_str()));
    }
}

#[test]
fn only_capitalised_ascii_segments_under_the_root_have_an_alias() {
    assert_eq!(alias_spelling("Elixir"), Some("Elixir"));
    assert_eq!(alias_spelling("Elixir.F"), Some("F"));
    for no_alias in [
        "Foo",
        "Elixirs.Foo",
        "Elixir.",
        "Elixir.lower",
        "Elixir.Foo.bar",
        "Elixir.Foo?",
        "Elixir.Foo..Bar",
        "Elixir.Foo.",
        "Elixir.Fo-o",
        "Elixir.Ä",
    ] {
        assert_eq!(alias_spelling(no_alias), None, "{no_alias} is not alias-shaped");
    }
}

#[test]
fn the_alias_namespace_is_every_atom_under_the_root_whatever_its_shape() {
    assert!(is_alias_namespace_atom("Elixir.Foo"));
    assert!(is_alias_namespace_atom("Elixir.lower"));
    assert!(!is_alias_namespace_atom("Elixir"));
    assert!(!is_alias_namespace_atom("Elixirs.Foo"));
    assert!(!is_alias_namespace_atom("a"));
}
