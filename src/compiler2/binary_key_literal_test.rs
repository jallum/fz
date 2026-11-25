//! A map literal types the values of the keys it writes, whatever the keys
//! are. Fixture 1871 builds literals keyed by binaries, alone and mixed with
//! atoms, reads them back, and changes them with `Map.put`, a map update and
//! `Map.merge`; these tests read back the types it settles to.

use super::Ty;
use super::drive_harness::Drive;
use super::drive_harness::Settled;
use super::types::KeyAt;
use super::types::MapDomain;
use super::types::MapKey;
use super::types::MapTypeEntry;
use super::types::MapTypeKey;
use super::types::Types;

const FIXTURE: u32 = 1871;

fn returned(settled: &mut Settled, name: &str) -> Ty {
    let function = settled.function(name, 0);
    settled
        .return_types()
        .last_for_function(settled.root(), function)
        .return_ty
}

fn assert_returns(settled: &mut Settled, name: &str, expected: impl FnOnce(&mut Types) -> Ty, intent: &str) {
    let actual = returned(settled, name);
    let expected = expected(settled.compiler_mut().types_mut_for_test());
    assert!(
        settled.compiler().types_equivalent_for_test(actual, expected),
        "{intent}: {name}/0 settles to `{}`, expected `{}`",
        settled.compiler().display_ty_for_test(actual),
        settled.compiler().display_ty_for_test(expected),
    );
}

fn union_of(types: &mut Types, parts: &[Ty]) -> Ty {
    let mut joined = types.none();
    for part in parts {
        joined = types.union(joined, *part);
    }
    joined
}

fn binary_domain(types: &mut Types, value: Ty) -> Ty {
    let entry = MapTypeEntry {
        key: MapTypeKey::Domain(MapDomain::Binary),
        optional: true,
        value,
    };
    types.map_literal_of_entries(&[entry])
}

#[test]
fn a_literal_keyed_by_binaries_is_a_map_whose_binary_keys_hold_its_values() {
    let mut settled = Drive::fixture(FIXTURE).settle();

    assert_returns(
        &mut settled,
        "table",
        |types| {
            let int = types.int();
            binary_domain(types, int)
        },
        "every value of the literal is an int, so every binary key holds one",
    );
}

#[test]
fn the_values_of_several_binary_keys_join_in_the_one_binary_domain() {
    let mut settled = Drive::fixture(FIXTURE).settle();

    assert_returns(
        &mut settled,
        "floats",
        |types| {
            let (int, float) = (types.int(), types.float());
            let joined = union_of(types, &[int, float]);
            binary_domain(types, joined)
        },
        "the int and the float both live under binary keys",
    );
}

#[test]
fn a_literal_mixing_atom_and_binary_keys_names_the_atom_and_types_the_binaries() {
    let mut settled = Drive::fixture(FIXTURE).settle();
    let mixed = returned(&mut settled, "mixed");
    let types = settled.compiler_mut().types_mut_for_test();
    let int = types.int();

    let named = types.value_at(&mixed, &KeyAt::Exact(MapKey::Atom("a".into())));
    let binary = types.str_t();
    let by_binary = types.value_at(&mixed, &KeyAt::OfType(binary));

    assert_eq!(
        named,
        Some(int),
        "`:a` is a required field holding the int written for it"
    );
    assert_eq!(by_binary, Some(int), "the binary key's value is the domain's type");
}

#[test]
fn reading_a_binary_keyed_literal_answers_the_value_type_through_every_reader() {
    let mut settled = Drive::fixture(FIXTURE).settle();

    assert_returns(
        &mut settled,
        "pattern_of_table",
        |types| types.int(),
        "a pattern binds the value",
    );
    assert_returns(
        &mut settled,
        "access_of_table",
        |types| {
            let (int, nil) = (types.int(), types.nil());
            types.union(int, nil)
        },
        "m[k] composes nil for a miss",
    );
    assert_returns(
        &mut settled,
        "get_of_table",
        |types| {
            let (int, none) = (types.int(), types.atom_lit("none"));
            types.union(int, none)
        },
        "Map.get/3 composes its default for a miss",
    );
    assert_returns(
        &mut settled,
        "pattern_of_floats",
        |types| {
            let (int, float) = (types.int(), types.float());
            types.union(int, float)
        },
        "a binary key may hold either value the literal wrote under binary keys",
    );
    assert_returns(
        &mut settled,
        "pattern_of_mixed",
        |types| types.int(),
        "mixed literal's binary key",
    );
}

#[test]
fn a_map_update_that_writes_another_type_widens_the_binary_domain() {
    let mut settled = Drive::fixture(FIXTURE).settle();

    assert_returns(
        &mut settled,
        "after_update",
        |types| {
            let (int, binary) = (types.int(), types.str_t());
            types.union(int, binary)
        },
        "the update writes a binary under a key the literal held an int under",
    );
}

#[test]
fn put_and_merge_never_leave_a_narrower_domain_than_what_they_wrote() {
    let mut settled = Drive::fixture(FIXTURE).settle();

    for (name, written) in [("after_put", "binary"), ("after_merge", "atom")] {
        let result = returned(&mut settled, name);
        let types = settled.compiler_mut().types_mut_for_test();
        let written = match written {
            "binary" => types.str_t(),
            _ => types.atom_lit("atom"),
        };
        assert!(
            types.is_subtype(&written, &result),
            "{name}/0 writes a value of a type the literal's domain did not hold, so its read must include it",
        );
    }
}
