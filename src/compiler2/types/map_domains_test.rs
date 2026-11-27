//! A map type holds named fields and, for every other key, a domain per kind
//! of key. These tests state what the lattice answers across fields and
//! domains: an absent key satisfies a domain, a present one must fit it.

use super::{KeyAt, MapDomain, MapKey, MapTypeEntry, MapTypeKey, Ty, Types};

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

fn exact(name: &str) -> KeyAt {
    KeyAt::Exact(MapKey::Atom(name.to_string()))
}

/// `%{required(name) => value}` (or optional): one named atom field, every
/// domain left open.
fn named(t: &mut Types, name: &str, value: Ty) -> Ty {
    field(t, name, value, false)
}

fn assert_value(t: &mut Types, read: Option<Ty>, expected: Ty, intent: &str) {
    let read = read.unwrap_or_else(|| panic!("{intent}: the lookup answered None"));
    assert!(
        t.is_equivalent(&read, &expected),
        "{intent}: read `{}`, expected `{}`",
        t.display(&read),
        t.display(&expected),
    );
}

// Census row (a): a literal key the map names.

#[test]
fn a_named_required_field_reads_its_type_and_cannot_miss() {
    let mut t = Types::new();
    let int = t.int();
    let map = named(&mut t, "a", int);

    let read = t.value_at(&map, &exact("a"));

    assert_value(&mut t, read, int, "a named field answers its own type");
    assert!(!t.can_miss(&map, &exact("a")), "a required field is always there");
}

#[test]
fn a_named_optional_field_reads_its_type_without_nil_and_can_miss() {
    let mut t = Types::new();
    let binary = t.str_t();
    let map = field(&mut t, "b", binary, true);

    let read = t.value_at(&map, &exact("b"));

    assert_value(
        &mut t,
        read,
        binary,
        "the value WHEN PRESENT: absence is the caller's `nil`, not the lookup's",
    );
    assert!(t.can_miss(&map, &exact("b")), "an optional field may be absent");
}

// Census row (b): a literal key the map does not name.

#[test]
fn an_atom_the_map_does_not_name_reads_the_atom_domain_and_can_miss() {
    let mut t = Types::new();
    let int = t.int();
    let by_atom = domain(&mut t, MapDomain::Atom, int);

    let read = t.value_at(&by_atom, &exact("zzz"));

    assert_value(&mut t, read, int, "an unnamed atom key is held by the atom domain");
    assert!(t.can_miss(&by_atom, &exact("zzz")), "a domain never requires a key");
}

#[test]
fn an_atom_a_map_leaves_unconstrained_reads_any() {
    let mut t = Types::new();
    let int = t.int();
    let any = t.any();
    let named_atom_only = named(&mut t, "a", int);

    let read = t.value_at(&named_atom_only, &exact("zzz"));

    assert_value(
        &mut t,
        read,
        any,
        "a type that writes no key kind is open: other keys hold anything",
    );
    assert!(t.can_miss(&named_atom_only, &exact("zzz")));
}

// Census row (c): a key known only by its type, a binary.

#[test]
fn a_binary_key_reads_the_binary_domain_without_nil_and_can_miss() {
    let mut t = Types::new();
    let (binary, int) = (t.str_t(), t.int());
    let by_binary = domain(&mut t, MapDomain::Binary, int);

    let read = t.value_at(&by_binary, &KeyAt::OfType(binary));

    assert_value(&mut t, read, int, "a binary key addresses the binary domain");
    assert!(
        t.can_miss(&by_binary, &KeyAt::OfType(binary)),
        "a key known by its type may be absent"
    );
}

// Census row (d): a non-literal key of a known type.

/// A type that writes a key kind holds only keys of the kinds it writes, so a
/// key of any other kind is never present: the value it holds is `none`, and
/// a read of it answers `nil` alone.
#[test]
fn a_key_of_a_kind_the_type_does_not_write_holds_nothing() {
    let mut t = Types::new();
    let (int, atom, none) = (t.int(), t.atom(), t.none());
    let by_binary = domain(&mut t, MapDomain::Binary, int);

    let by_type = t.value_at(&by_binary, &KeyAt::OfType(atom));
    let by_name = t.value_at(&by_binary, &exact("zzz"));

    assert_value(
        &mut t,
        by_type,
        none,
        "an atom-typed key on a map that writes only binary keys",
    );
    assert_value(&mut t, by_name, none, "the atom `:zzz` on that map");
    assert!(t.can_miss(&by_binary, &exact("zzz")), "so the reader answers `nil`");
}

/// A type that writes several key kinds holds each of them and no other.
#[test]
fn a_type_that_writes_two_key_kinds_holds_those_two() {
    let mut t = Types::new();
    let (int, float, none) = (t.int(), t.float(), t.none());
    let binary_or_atom = t.map_of_entries(&[
        MapTypeEntry {
            key: MapTypeKey::Domain(MapDomain::Binary),
            optional: true,
            value: int,
        },
        MapTypeEntry {
            key: MapTypeKey::Domain(MapDomain::Atom),
            optional: true,
            value: float,
        },
    ]);
    let binary = t.str_t();
    let by_binary = t.value_at(&binary_or_atom, &KeyAt::OfType(binary));
    let by_atom = t.value_at(&binary_or_atom, &exact("zzz"));
    let by_int = t.value_at(&binary_or_atom, &KeyAt::OfType(int));

    assert_value(&mut t, by_binary, int, "a binary key reads the binary domain");
    assert_value(&mut t, by_atom, float, "an atom key reads the atom domain");
    assert_value(
        &mut t,
        by_int,
        none,
        "an integer key is of a kind the type does not write",
    );
}

/// A literal that writes a key kind is a map of that kind alone, as a written
/// type is: it holds no key of another kind.
#[test]
fn a_literal_with_a_key_known_by_type_holds_no_key_of_another_kind() {
    let mut t = Types::new();
    let (int, none) = (t.int(), t.none());
    let literal = t.map_literal_of_entries(&[MapTypeEntry {
        key: MapTypeKey::Domain(MapDomain::Binary),
        optional: true,
        value: int,
    }]);

    let read = t.value_at(&literal, &exact("zzz"));

    assert_value(&mut t, read, none, "a literal's unwritten kinds are absent");
}

/// A type that writes a key kind prints the kinds it writes and no others.
#[test]
fn a_type_that_writes_a_key_kind_prints_only_the_kinds_it_writes() {
    let mut t = Types::new();
    let int = t.int();
    let by_binary = domain(&mut t, MapDomain::Binary, int);

    assert_eq!(t.display(&by_binary), "%{binary => int}");
}

/// An open type prints only what it constrains, so the kinds it leaves free are
/// not named.
#[test]
fn a_type_that_writes_no_key_kind_prints_only_its_fields() {
    let mut t = Types::new();
    let int = t.int();
    let named_a = named(&mut t, "a", int);

    assert_eq!(t.display(&named_a), "%{:a: int}");
}

/// A type written with only atom keys writes no key kind, so it stays open: a
/// wider map still belongs to it.
#[test]
fn a_type_that_writes_only_named_atom_keys_stays_open() {
    let mut t = Types::new();
    let int = t.int();
    let named_a = named(&mut t, "a", int);
    let wider = t.map(&[
        (MapKey::Atom("a".to_string()), int),
        (MapKey::Atom("b".to_string()), int),
    ]);
    let by_binary_too = {
        let by_binary = domain(&mut t, MapDomain::Binary, int);
        t.intersect(wider, by_binary)
    };

    assert!(t.is_subtype(&wider, &named_a));
    assert!(t.is_subtype(&by_binary_too, &named_a));
}

#[test]
fn an_atom_key_type_joins_the_named_atom_fields_with_the_atom_domain() {
    let mut t = Types::new();
    let (int, float, atom) = (t.int(), t.float(), t.atom());
    let named_x = MapTypeEntry {
        key: MapTypeKey::Literal(MapKey::Atom("x".to_string())),
        optional: false,
        value: int,
    };
    let by_atom = MapTypeEntry {
        key: MapTypeKey::Domain(MapDomain::Atom),
        optional: true,
        value: float,
    };
    let map = t.map_of_entries(&[named_x, by_atom]);

    let read = t.value_at(&map, &KeyAt::OfType(atom));

    let number = t.union(int, float);
    assert_value(&mut t, read, number, "any atom may be `:x` or another atom");
}

#[test]
fn a_key_type_naming_one_atom_reads_that_field() {
    let mut t = Types::new();
    let int = t.int();
    let map = named(&mut t, "a", int);
    let only_a = t.atom_lit("a");

    let read = t.value_at(&map, &KeyAt::OfType(only_a));

    assert_value(&mut t, read, int, "a pinned variable known to be `:a` reads field `a`");
}

// Census row (e): a key nobody knows.

#[test]
fn a_key_that_is_no_kind_of_key_has_no_answer() {
    let mut t = Types::new();
    let int = t.int();
    let by_binary = domain(&mut t, MapDomain::Binary, int);
    let unsolved = t.param_alpha(0);

    assert_eq!(
        t.value_at(&by_binary, &KeyAt::OfType(unsolved)),
        None,
        "a type variable is not a kind of key"
    );
}

#[test]
fn a_key_nothing_is_known_of_has_no_answer_and_the_reader_says_any() {
    let mut t = Types::new();
    let (int, any) = (t.int(), t.any());
    let by_binary = domain(&mut t, MapDomain::Binary, int);

    assert_eq!(
        t.value_at(&by_binary, &KeyAt::OfType(any)),
        None,
        "`any` is not a kind of key: the reader falls back to `any`"
    );
}

// Census row (f): a union of maps.

#[test]
fn a_union_of_maps_joins_what_each_member_holds() {
    let mut t = Types::new();
    let (int, binary) = (t.int(), t.str_t());
    let first = named(&mut t, "a", int);
    let second = named(&mut t, "a", binary);
    let either = t.union(first, second);

    let read = t.value_at(&either, &exact("a"));

    let expected = t.union(int, binary);
    assert_value(&mut t, read, expected, "each member holds its own `a`");
    assert!(!t.can_miss(&either, &exact("a")), "every member requires `a`");
}

#[test]
fn a_union_whose_member_does_not_name_the_key_reads_any_and_can_miss() {
    let mut t = Types::new();
    let (int, binary, any) = (t.int(), t.str_t(), t.any());
    let has_a = named(&mut t, "a", int);
    let has_b = named(&mut t, "b", binary);
    let either = t.union(has_a, has_b);

    let read = t.value_at(&either, &exact("a"));

    assert_value(&mut t, read, any, "the second member is open at `a`");
    assert!(t.can_miss(&either, &exact("a")), "one member lacks `a`");
}

// Census row (g): any, and what is no map.

#[test]
fn any_reads_any_and_can_miss() {
    let mut t = Types::new();
    let any = t.any();

    let read = t.value_at(&any, &exact("a"));

    assert_value(&mut t, read, any, "an unknown value may be a map holding anything");
    assert!(t.can_miss(&any, &exact("a")), "an arbitrary map proves nothing");
}

#[test]
fn a_type_with_no_map_in_it_holds_no_key() {
    let mut t = Types::new();
    let int = t.int();

    assert_eq!(t.value_at(&int, &exact("a")), None, "no member can hold the key");
    assert_eq!(t.value_at(&int, &KeyAt::OfType(int)), None);
    assert!(t.can_miss(&int, &exact("a")), "a non-map has no keys");
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

/// A map type that names the atom `:x` and writes the binary kind, updated
/// at an atom key: `:x` may now hold the new value too, and the binary kind
/// is untouched.
#[test]
fn updating_at_an_atom_key_known_by_type_widens_the_named_atom_fields_and_the_kinds_the_type_writes() {
    let mut t = Types::new();
    let (atom, int, float) = (t.atom(), t.int(), t.float());
    let map = t.map_of_entries(&[
        MapTypeEntry {
            key: MapTypeKey::Literal(MapKey::Atom("x".to_string())),
            optional: false,
            value: int,
        },
        MapTypeEntry {
            key: MapTypeKey::Domain(MapDomain::Binary),
            optional: true,
            value: int,
        },
    ]);

    let updated = t
        .widen_map_at_key_type(&map, &atom, &float)
        .expect("atom is a kind of key");

    let number = t.union(int, float);
    let read = t.value_at(&updated, &exact("x")).expect("x is held");
    assert!(t.is_equivalent(&read, &number));
    let binary = t.str_t();
    let binary_values = t.value_at(&updated, &KeyAt::OfType(binary));
    assert_value(&mut t, binary_values, int, "the binary kind is left as it was");
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
