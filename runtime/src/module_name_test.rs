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

#[test]
fn a_bare_atom_is_a_module_named_by_itself() {
    let erlang = ModuleName::bare_atom("erlang");
    assert_eq!(erlang.atom_name(), "erlang");
    assert_eq!(ModuleName::from_atom_name("erlang"), Some(erlang));
}

#[test]
fn an_elixir_prefixed_atom_is_the_dotted_module() {
    assert_eq!(
        ModuleName::from_atom_name("Elixir.Foo.Bar"),
        Some(name(&["Foo", "Bar"]))
    );
}

#[test]
fn every_module_maps_to_its_atom_and_back() {
    for module in [
        name(&["Foo"]),
        name(&["Foo", "Bar"]),
        ModuleName::bare_atom("erlang"),
        ModuleName::bare_atom("my_atom_mod"),
    ] {
        assert_eq!(ModuleName::from_atom_name(&module.atom_name()), Some(module));
    }
}

#[test]
fn a_bare_capitalised_atom_is_not_the_alias_of_the_same_spelling() {
    assert_ne!(ModuleName::bare_atom("Foo"), name(&["Foo"]));
    assert_eq!(ModuleName::bare_atom("Foo").atom_name(), "Foo");
}

#[test]
fn an_atom_that_starts_the_alias_namespace_but_has_no_path_names_no_module() {
    assert_eq!(ModuleName::from_atom_name("Elixir."), None);
    assert_eq!(ModuleName::from_atom_name("Elixir.Foo..Bar"), None);
    assert_eq!(ModuleName::from_atom_name(""), None);
}

#[test]
fn a_module_spells_itself_as_source_does() {
    assert_eq!(ModuleName::bare_atom("erlang").to_string(), ":erlang");
    assert_eq!(name(&["Foo", "Bar"]).to_string(), "Foo.Bar");
    assert_eq!(
        ModuleName::parse_dotted(":erlang").unwrap(),
        ModuleName::bare_atom("erlang")
    );
}
