//! Every way to read a value out of a map type asks the one lookup, so they
//! agree on what the map holds. Fixtures 01869 and 01870 read a typed map
//! through patterns, `Map.get`, `Map.fetch`, `Map.fetch!` and `m[k]`; these
//! tests read back the return type each function settles to.

use super::Ty;
use super::drive_harness::Drive;
use super::drive_harness::Settled;
use super::types::Types;

const PATTERNS: u32 = 1869;
const READS: u32 = 1870;
const KEY_KINDS: u32 = 1156;

/// Asserts the settled return type of `name/arity` is `expected(types)`.
fn assert_returns(
    settled: &mut Settled,
    name: &str,
    arity: u64,
    expected: impl FnOnce(&mut Types) -> Ty,
    intent: &str,
) {
    let function = settled.functions().id_in_module("Main", name, arity);
    let actual = settled
        .return_types()
        .last_for_function(settled.root(), function)
        .return_ty;
    let expected = expected(settled.compiler_mut().types_mut_for_test());
    assert!(
        settled.compiler().types_equivalent_for_test(actual, expected),
        "{intent}: {name}/{arity} settles to `{}`, expected `{}`",
        settled.compiler().display_ty_for_test(actual),
        settled.compiler().display_ty_for_test(expected),
    );
}

fn int(types: &mut Types) -> Ty {
    types.int()
}

fn list_of_int(types: &mut Types) -> Ty {
    let int = types.int();
    types.list(int)
}

#[test]
fn a_binary_key_pattern_binds_the_value_the_map_holds_under_binary_keys() {
    let mut settled = Drive::fixture(PATTERNS).settle();

    assert_returns(&mut settled, "in_case", 1, int, "a case clause");
    assert_returns(&mut settled, "in_head", 1, int, "a function head");
    assert_returns(&mut settled, "in_for", 1, list_of_int, "a for generator pattern");
    assert_returns(&mut settled, "in_enum_map", 1, list_of_int, "an Enum.map closure head");
}

#[test]
fn a_float_key_pattern_binds_the_value_the_map_holds_under_float_keys() {
    let mut settled = Drive::fixture(PATTERNS).settle();

    assert_returns(
        &mut settled,
        "in_float_case",
        1,
        int,
        "a float key addresses the float domain",
    );
}

#[test]
fn reading_one_typed_map_answers_the_same_value_whatever_the_reader() {
    let mut settled = Drive::fixture(READS).settle();
    let with = |types: &mut Types, extra: Ty| {
        let int = types.int();
        types.union(int, extra)
    };

    assert_returns(&mut settled, "pinned", 2, int, "a pinned key pattern proves presence");
    assert_returns(&mut settled, "fetch!", 2, int, "Map.fetch! raises on a miss");
    assert_returns(
        &mut settled,
        "get2",
        2,
        |types| {
            let nil = types.nil();
            with(types, nil)
        },
        "Map.get/2 composes nil for a miss",
    );
    assert_returns(
        &mut settled,
        "access",
        2,
        |types| {
            let nil = types.nil();
            with(types, nil)
        },
        "m[k] composes nil for a miss",
    );
    assert_returns(
        &mut settled,
        "get3",
        2,
        |types| {
            let none = types.atom_lit("none");
            with(types, none)
        },
        "Map.get/3 composes the default for a miss",
    );
    assert_returns(
        &mut settled,
        "fetch",
        2,
        |types| {
            let (int, ok, error) = (types.int(), types.atom_lit("ok"), types.atom_lit("error"));
            let found = types.tuple(&[ok, int]);
            types.union(found, error)
        },
        "Map.fetch answers {:ok, value} or :error",
    );
}

/// A map type that writes the binary kind holds binary keys only, so a read
/// at an atom answers `nil` and a read at a binary answers the value or `nil`.
#[test]
fn a_map_typed_by_binary_keys_reads_nil_at_an_atom_and_the_value_or_nil_at_a_binary() {
    let mut settled = Drive::fixture(KEY_KINDS).settle();

    assert_returns(
        &mut settled,
        "at_atom",
        1,
        |types| types.nil(),
        "no atom key can be present",
    );
    assert_returns(
        &mut settled,
        "at_binary",
        2,
        |types| {
            let (int, nil) = (types.int(), types.nil());
            types.union(int, nil)
        },
        "a binary key reads the binary domain or misses",
    );
}
