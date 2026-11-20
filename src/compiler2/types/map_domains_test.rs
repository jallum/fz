//! A map type holds named fields and, for every other key, a domain per kind
//! of key. These tests state what the lattice answers across fields and
//! domains: an absent key satisfies a domain, a present one must fit it.

use super::{MapDomain, MapKey, MapTypeEntry, MapTypeKey, Ty, Types};

fn domain(t: &mut Types, kind: MapDomain, value: Ty) -> Ty {
    t.map_of_entries(&[MapTypeEntry {
        key: MapTypeKey::Domain(kind),
        optional: true,
        value,
    }])
}

fn field(t: &mut Types, name: &str, value: Ty, optional: bool) -> Ty {
    t.map_of_entries(&[MapTypeEntry {
        key: MapTypeKey::Literal(MapKey::Atom(name.to_string())),
        optional,
        value,
    }])
}

#[test]
fn an_open_map_is_the_map_whose_every_domain_is_any() {
    let mut t = Types::new();
    let any = t.any();
    let every_domain: Vec<MapTypeEntry> = MapDomain::ALL
        .into_iter()
        .map(|kind| MapTypeEntry {
            key: MapTypeKey::Domain(kind),
            optional: true,
            value: any,
        })
        .collect();
    let spelled_out = t.map_of_entries(&every_domain);
    let open = t.map_top();

    assert!(t.is_equivalent(&spelled_out, &open));
}

#[test]
fn a_domain_map_is_a_subtype_of_the_open_map_and_not_the_reverse() {
    let mut t = Types::new();
    let (binary, int) = (t.str_t(), t.int());
    let by_binary = domain(&mut t, MapDomain::Binary, int);
    let open = t.map_top();
    let _ = binary;

    assert!(t.is_subtype(&by_binary, &open));
    assert!(!t.is_subtype(&open, &by_binary));
}

#[test]
fn a_domain_whose_values_fit_a_wider_domain_is_a_subtype() {
    let mut t = Types::new();
    let (int, float) = (t.int(), t.float());
    let number = t.union(int, float);
    let ints = domain(&mut t, MapDomain::Binary, int);
    let numbers = domain(&mut t, MapDomain::Binary, number);

    assert!(t.is_subtype(&ints, &numbers));
    assert!(!t.is_subtype(&numbers, &ints));
}

#[test]
fn a_domain_constrains_only_its_own_kind_of_key() {
    let mut t = Types::new();
    let (int, float) = (t.int(), t.float());
    let by_binary = domain(&mut t, MapDomain::Binary, int);
    let by_atom = domain(&mut t, MapDomain::Atom, float);

    assert!(!t.is_subtype(&by_binary, &by_atom));
    assert!(!t.is_subtype(&by_atom, &by_binary));
}

#[test]
fn two_domains_over_one_kind_of_key_still_admit_the_map_with_no_such_key() {
    // A domain is never required, so `%{}` satisfies both and the meet is
    // inhabited even when the value types are disjoint.
    let mut t = Types::new();
    let (int, atom) = (t.int(), t.atom());
    let ints = domain(&mut t, MapDomain::Binary, int);
    let atoms = domain(&mut t, MapDomain::Binary, atom);

    let meet = t.intersect(ints, atoms);
    let none = t.none();
    let only_the_absent_key = domain(&mut t, MapDomain::Binary, none);

    assert!(!t.is_empty(&meet));
    assert!(!t.is_disjoint(&ints, &atoms));
    assert!(t.is_equivalent(&meet, &only_the_absent_key));
}

#[test]
fn a_required_field_is_disjoint_from_a_domain_that_holds_an_incompatible_type() {
    let mut t = Types::new();
    let (int, atom) = (t.int(), t.atom());
    let named_atom = field(&mut t, "a", atom, false);
    let atoms_hold_ints = domain(&mut t, MapDomain::Atom, int);

    assert!(t.is_disjoint(&named_atom, &atoms_hold_ints));
    let meet = t.intersect(named_atom, atoms_hold_ints);
    assert!(t.is_empty(&meet));
}

#[test]
fn an_optional_field_is_not_disjoint_from_a_domain_that_holds_an_incompatible_type() {
    let mut t = Types::new();
    let (int, atom) = (t.int(), t.atom());
    let maybe_atom = field(&mut t, "a", atom, true);
    let atoms_hold_ints = domain(&mut t, MapDomain::Atom, int);

    assert!(!t.is_disjoint(&maybe_atom, &atoms_hold_ints));
}

#[test]
fn a_required_field_is_a_subtype_of_the_same_field_optional_and_not_the_reverse() {
    let mut t = Types::new();
    let int = t.int();
    let required = field(&mut t, "x", int, false);
    let optional = field(&mut t, "x", int, true);

    assert!(t.is_subtype(&required, &optional));
    assert!(!t.is_subtype(&optional, &required));
}

#[test]
fn a_field_agrees_with_a_domain_over_its_kind_of_key_when_its_value_does() {
    let mut t = Types::new();
    let (int, float) = (t.int(), t.float());
    let named_int = field(&mut t, "x", int, false);
    let atoms_hold_ints = domain(&mut t, MapDomain::Atom, int);
    let atoms_hold_floats = domain(&mut t, MapDomain::Atom, float);

    assert!(!t.is_disjoint(&named_int, &atoms_hold_ints));
    assert!(t.is_disjoint(&named_int, &atoms_hold_floats));
}

#[test]
fn the_difference_of_a_domain_map_and_its_supertype_is_empty() {
    let mut t = Types::new();
    let (int, float) = (t.int(), t.float());
    let number = t.union(int, float);
    let ints = domain(&mut t, MapDomain::Binary, int);
    let numbers = domain(&mut t, MapDomain::Binary, number);

    let narrower = t.difference(ints, numbers);
    let wider = t.difference(numbers, ints);

    assert!(t.is_empty(&narrower));
    assert!(!t.is_empty(&wider));
}

#[test]
fn a_map_limiting_another_kind_of_key_leaves_a_remainder_when_removed() {
    // `%{binary => int} \ %{atom => int}`: a map in the first may hold an
    // atom key of any value, which the second does not contain, so the
    // remainder is inhabited and the first is not wholly inside the second.
    let mut t = Types::new();
    let int = t.int();
    let by_binary = domain(&mut t, MapDomain::Binary, int);
    let by_atom = domain(&mut t, MapDomain::Atom, int);

    let rest = t.difference(by_binary, by_atom);

    assert!(!t.is_empty(&rest));
    assert!(!t.is_subtype(&by_binary, &by_atom));
}

#[test]
fn a_type_recursive_through_a_map_domain_admits_its_own_nesting() {
    // `decode_value = integer | binary | [decode_value] | %{binary => decode_value}`
    let mut t = Types::new();
    let decode_value = t.recursive(1, |t, me| {
        let (int, binary) = (t.int(), t.str_t());
        let list = t.list(me[0]);
        let map = domain(t, MapDomain::Binary, me[0]);
        let scalars = t.union(int, binary);
        let nested = t.union(list, map);
        vec![t.union(scalars, nested)]
    })[0];
    let int = t.int();
    let ints = domain(&mut t, MapDomain::Binary, int);
    let nested_once = domain(&mut t, MapDomain::Binary, ints);
    let atom = t.atom();
    let atoms = domain(&mut t, MapDomain::Binary, atom);

    assert!(!t.is_empty(&decode_value));
    assert!(t.is_subtype(&ints, &decode_value));
    assert!(t.is_subtype(&nested_once, &decode_value));
    assert!(!t.is_subtype(&atoms, &decode_value));
}

#[test]
fn a_key_kind_is_read_from_a_key_type() {
    let mut t = Types::new();
    let (binary, int, atom) = (t.str_t(), t.int(), t.atom());
    let key = t.union(binary, int);
    let kinds = t.map_key_kinds(&key).expect("a union of scalars is a kind of key");

    assert!(kinds.atoms.is_empty());
    assert_eq!(kinds.domains.len(), 2);
    assert!(kinds.domains.contains(&MapDomain::Binary));
    assert!(kinds.domains.contains(&MapDomain::Integer));
    let atoms = t.map_key_kinds(&atom).expect("atom is a kind of key");
    assert_eq!(atoms.domains, vec![MapDomain::Atom]);
}

#[test]
fn reading_a_key_known_by_type_answers_its_domain_beside_nil() {
    let mut t = Types::new();
    let (binary, int, nil) = (t.str_t(), t.int(), t.nil());
    let by_binary = domain(&mut t, MapDomain::Binary, int);

    let read = t.domain_lookup(&by_binary, &binary).expect("a binary is a kind of key");

    let expected = t.union(int, nil);
    assert!(t.is_equivalent(&read, &expected));
}

#[test]
fn reading_a_key_of_a_kind_the_map_leaves_free_answers_any() {
    let mut t = Types::new();
    let (int, atom) = (t.int(), t.atom());
    let by_binary = domain(&mut t, MapDomain::Binary, int);

    let read = t.domain_lookup(&by_binary, &atom).expect("an atom is a kind of key");

    let any = t.any();
    assert!(t.is_equivalent(&read, &any));
}

#[test]
fn reading_an_atom_key_joins_the_named_atom_fields_with_the_atom_domain() {
    let mut t = Types::new();
    let (int, float, atom, nil) = (t.int(), t.float(), t.atom(), t.nil());
    let named = MapTypeEntry {
        key: MapTypeKey::Literal(MapKey::Atom("x".to_string())),
        optional: false,
        value: int,
    };
    let atoms = MapTypeEntry {
        key: MapTypeKey::Domain(MapDomain::Atom),
        optional: true,
        value: float,
    };
    let map = t.map_of_entries(&[named, atoms]);

    let read = t.domain_lookup(&map, &atom).expect("an atom is a kind of key");

    let number = t.union(int, float);
    let expected = t.union(number, nil);
    assert!(t.is_equivalent(&read, &expected));
}

#[test]
fn updating_at_a_key_known_by_type_widens_that_kinds_domain() {
    let mut t = Types::new();
    let (binary, int, float) = (t.str_t(), t.int(), t.float());
    let ints = domain(&mut t, MapDomain::Binary, int);

    let updated = t
        .widen_map_at_key_type(&ints, &binary, &float)
        .expect("binary is a kind of key");

    let number = t.union(int, float);
    let numbers = domain(&mut t, MapDomain::Binary, number);
    assert!(t.is_equivalent(&updated, &numbers));
}

#[test]
fn updating_at_an_atom_key_known_by_type_widens_named_atom_fields_and_leaves_other_kinds() {
    let mut t = Types::new();
    let (atom, int, float) = (t.atom(), t.int(), t.float());
    let named = field(&mut t, "x", int, false);
    let by_binary = domain(&mut t, MapDomain::Binary, int);
    let map = t.intersect(named, by_binary);

    let updated = t
        .widen_map_at_key_type(&map, &atom, &float)
        .expect("atom is a kind of key");

    let number = t.union(int, float);
    let widened_named = field(&mut t, "x", number, false);
    let expected = t.intersect(widened_named, by_binary);
    let read = t
        .field_lookup(&updated, &MapKey::Atom("x".to_string()))
        .expect("x is held");
    assert!(t.is_equivalent(&read, &number));
    assert!(t.is_subtype(&updated, &expected));
    assert!(t.is_subtype(&updated, &by_binary));
}

#[test]
fn a_literal_with_a_key_known_by_type_builds_a_domain_not_the_open_map() {
    let mut t = Types::new();
    let int = t.int();
    let literal = t.map_literal_of_entries(&[MapTypeEntry {
        key: MapTypeKey::Domain(MapDomain::Binary),
        optional: true,
        value: int,
    }]);
    let by_binary = domain(&mut t, MapDomain::Binary, int);
    let plain = t.plain_map();

    let open = t.map_top();
    assert!(t.is_subtype(&literal, &by_binary));
    assert!(t.is_subtype(&literal, &plain));
    assert!(!t.is_subtype(&open, &literal));
}

#[test]
fn updating_a_struct_at_atom_keys_that_exclude_its_module_key_keeps_the_struct() {
    // `%{point | k => v}` with `k` one of `:x | :y` cannot change what
    // `__struct__` names; with `k` any atom it can.
    let mut t = Types::new();
    let (int, float, atom) = (t.int(), t.float(), t.atom());
    let point = t.struct_map(
        &crate::modules::identity::ModuleName::from_atom_name("Elixir.Pt").expect("a module name"),
        &[(MapKey::Atom("x".to_string()), int)],
    );
    let (x, y) = (t.atom_lit("x"), t.atom_lit("y"));
    let xy = t.union(x, y);

    let by_name = t.widen_map_at_key_type(&point, &xy, &float).expect("atoms are keys");
    let by_any_atom = t.widen_map_at_key_type(&point, &atom, &float).expect("atoms are keys");

    assert!(t.sole_struct(&by_name).is_some());
    assert!(t.sole_struct(&by_any_atom).is_none());
}
